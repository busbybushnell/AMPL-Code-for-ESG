### NOTES: This runs a multi-firm dispatch model
### AND AN EMISSIONS CAP - FIRMS CAN BE ASSIGNED COURNOT OR COMPETITIVE
### THIS VERSION IS DESIGNED TO SOLVE MANY HOURS SIMULTANEOUSLY

set DAY;
set HOUR;	
set FIRMS;												# indexes multiple locations

set	REGION;	
set INREGION within REGION;														# Identifies the region that is the 'slack' bus or region
set OUTREGION within REGION;													# Identifies regions that are NOT the slack bus 
set ALLUNITS := {1..100} ordered; 												# indexes units 
set UNITS within {ALLUNITS,FIRMS,REGION};   									#indexes units by FIRM and 
set CAPREGION within REGION;
set NOCAP := REGION diff CAPREGION;											#indexes regions with no cap

set TLINES;

param firmtype {FIRMS}; 		# 1	is competitive, 2 is COURNOT
set COURNOT := {i in FIRMS: firmtype[i] > 1};
set COMP := FIRMS diff COURNOT;

#***************** Model Parameters *******************************


param mc {UNITS};       		 # constant marginal cost of multiple thermal production

param fixom {UNITS};       		 # fixed operating cost (daily)
param maxtherm {UNITS};

param a {REGION, DAY, HOUR};				      # intercept of regional demand
param b {REGION};        			   				# slope of regional demand curve

var p {REGION, DAY, HOUR};							#regional price

var totcost {r in REGION, d in DAY, h in HOUR};		

var q {(i,f,r) in UNITS, d in DAY, h in HOUR};         			  # output of units
var psi{ (i,f,r) in UNITS,d in DAY, h in HOUR};   			      # Dual on thermal capacity




#### Transmission related parameters and variables

param PTDF {l in TLINES, r in OUTREGION};
param FCAP {TLINES};									# transmission limits
var y {REGION, DAY, HOUR};								# Net injection from each OUTREGION to the slack bus
var gamma1   {l in TLINES, d in DAY, h in HOUR};		# shadow price on trans constraint (trans price)
var gamma2   {l in TLINES, d in DAY, h in HOUR};		# shadow price on trans constraint (trans price)


##### NOTE FOR NOW DEFINING Y (FLOWS) AS NEGATIVE POSITIVE - POSITIVE MEANS North TO South



### EMISSIONS RELATED VARIABLES

param E{UNITS};								# constant emissions rate of unit
param CARBONCAP;
#param lambda;								# shadow value on CAP constraint (price of carbon)
var lambda;								   # lambda is variable if solved endogenously


###
# Regional QUANTITY
###

var qregion {r in REGION, d in DAY, h in HOUR} = sum {f in FIRMS,(i,f,r) in UNITS} q[i,f,r,d,h];	

#######
# FIRM LEVEL ACCOUNTING VARIABLES
#######
		

#regional thermal production

var  qfirm {f in FIRMS, r in REGION, d in DAY, h in HOUR} = sum {(i,f,r) in UNITS} q[i,f,r,d,h];	

var  MR{f in FIRMS, r in REGION, d in DAY, h in HOUR} = p[r,d,h]+(qfirm[f,r,d,h])/b[r];

var  firmcost{f in FIRMS} = sum {r in REGION, (i,f,r) in UNITS, d in DAY, h in HOUR} (mc[i,f,r]*q[i,f,r,d,h] + fixom[i,f,r]*4);	

var  firmprofit{f in FIRMS} = sum {r in REGION, (i,f,r) in UNITS, d in DAY, h in HOUR} q[i,f,r,d,h]*p[r,d,h] - firmcost[f];
			
######
# EMISSIONS ACCOUNTING VARIABLES
######

var tonscarbon{d in DAY, h in HOUR} = sum {(i,f,r) in UNITS} (E[i,f,r]*q[i,f,r,d,h]);	

var CAP_CARBON = sum {d in DAY, h in HOUR} tonscarbon[d,h];

var region_demand {r in REGION, d in DAY, h in HOUR} = a[r,d,h] + b[r]*p[r,d,h];	

##########
## Market objective function: commented out for equilibrium version of the formulation
##########

#maximize SW: sum{r in REGION, d in DAY, h in HOUR} (0.5*(-a[r,d,h]/b[r] - p[r,d,h])*(qreg[r,d,h]) + p[r,d,h]*qreg[r,d,h])
#				- sum {f in FIRMS, r in REGION, (i,f,r) in UNITS, d in DAY, h in HOUR} (mc[i,f,r]*q[i,f,r,d,h]);



################
####### MARKET EQUILIBRIUM VARIABLES
####### Equilibrium conditions -MR = MC  for COURNOT firms, P = MC for FRINGE firms
################

subject to EQ1 {f in COMP, r in REGION, (i,f,r) in UNITS, d in DAY, h in HOUR}:
	q[i,f,r,d,h] >= 0 complements
	p[r,d,h] - mc[i,f,r] - E[i,f,r]*lambda - psi[i,f,r,d,h] <= 0;
	
subject to EQ2 {f in COURNOT, r in REGION, (i,f,r) in UNITS, d in DAY, h in HOUR}:
	q[i,f,r,d,h] >= 0 complements
	MR[f,r,d,h] - mc[i,f,r] - E[i,f,r]*lambda - psi[i,f,r,d,h] <= 0;		
	
subject to P1 {n in INREGION, d in DAY, h in HOUR}:
	p[n,d,h] = (a[n,d,h]- (sum {(i,f,n) in UNITS} q[i,f,n,d,h]) - (sum {r in OUTREGION} y[r,d,h]))/-b[n];	
	
subject to P2 {r in OUTREGION, d in DAY, h in HOUR}:
	p[r,d, h] = (a[r,d,h] - (sum {(i,f,r) in UNITS} q[i,f,r,d,h]) + y[r,d,h])/-b[r];
				
	

##########
## Production constraints - plant level capacity constraint
##########

subject to g1 {f in FIRMS, r in REGION, (i,f,r) in UNITS, d in DAY, h in HOUR}:	  
  psi[i,f,r,d,h] >= 0 complements
   maxtherm[i,f,r] - q[i,f,r,d,h]  >= 0;		# complement var is psi

   
##########
##	Transmission related constraints   
##########

subject to T1 {l in TLINES,d in DAY, h in HOUR}:							#complement is gamma1
	gamma1[l,d,h] >=0 complements
	FCAP[l] - (sum {r in OUTREGION} PTDF[l,r]*y[r,d,h]) >= 0;
	
subject to T2 {l in TLINES,d in DAY, h in HOUR}:							# complement is gamma2
	gamma2[l,d,h] >= 0 complements
	FCAP[l] + (sum {r in OUTREGION} PTDF[l,r]*y[r,d,h])  >= 0;
		

subject to T3 {d in DAY, h in HOUR}:
	sum {r in REGION} y[r,d,h] = 0;
		
		
subject to T4 {n in INREGION, s in OUTREGION,d in DAY, h in HOUR, l in TLINES}:
	p[s,d,h] - p[n,d,h] + gamma1[l,d,h] - gamma2[l,d,h] = 0;
	

########
## Emisssions CAP constraint
########


subject to E1a:
	lambda >=0 complements
	 CAP_CARBON <= CARBONCAP; 
