##### R Code Syntax for Ratcliff et al. paper titled "A 20-Year Review of Accession Characteristics in the U.S. Army"
## NOTE: Some linkage of data sources occurred ad-hoc to the original formation of the dataset.
## NOTE: for questions about the data or using the PDE, contact Nathaniel Ratcliff, email = nr3xe@virginia.edu

#### Data Input -----------------------------------------------------------
# Original date of linkage 2020-10-12
# Data for accession dates from 2000 to 2019 (20 years, inclusive); N = 1,440,282
data <- read.csv("\\\\facaa7pde01p\\PDE\\Projects\\ARI\\ARI-SDAL\\Army20Yr_linked_data_analytics.csv", header = TRUE, na.strings = c("NA", "NaN", "", " "), fill = TRUE)
data$DATE_BIRTH.CB <-lubridate::as_date(data$DATE_BIRTH.CB)
data$DATE_ACC.CB <-lubridate::as_date(data$DATE_ACC.CB)
data$ADSVC_PE_DT <-lubridate::as_date(data$ADSVC_PE_DT)
data$TXN_EFF_DT <-lubridate::as_date(data$TXN_EFF_DT)
names(data)
dplyr::as_tibble(head(data))
length(unique(data$PID_PDE))
# Filters for rank groups
data.e <- data %>% dplyr::filter(RANK_PDE_GRP == "Enlisted") %>% droplevels # N = 1,356,546
data.w <- data %>% dplyr::filter(RANK_PDE_GRP == "Warrant Officer") %>% droplevels # N = 598
data.o <- data %>% dplyr::filter(RANK_PDE_GRP == "Officer") %>% droplevels # 83,135

data <- data %>% dplyr::filter(RANK_PDE_GRP == "Enlisted") %>% droplevels # N = 1,356,546
data <- data %>% dplyr::filter(RANK_PDE_GRP == "Warrant Officer") %>% droplevels # N = 598
data <- data %>% dplyr::filter(RANK_PDE_GRP == "Officer") %>% droplevels # 83,135
data <- data %>% dplyr::filter(RANK_PDE_GRP == "Enlisted" | RANK_PDE_GRP == "Officer") %>% droplevels # N = 1,439,681
# filters for cohort
data.c <- data %>% dplyr::filter(cohort.2018 == TRUE)

#END
#### Optional Parameters -----------------------------------------------------------

## For data linkage

setwd("\\\\facaa7pde01p/PDE/Projects/ARI/ARI-SDAL")
# connect to database
source(file = file.path(getwd(), "analysis/utils/db_connect.R"))
con <- get_con(Sys.getenv("PDE_USER"), Sys.getenv("PDE_PW"))

## For data analysis

setwd("\\\\facaa7pde01p\\PDE\\Projects\\ARI\\ARI-SDAL\\analysis\\ratcliff\\ARI2\\EDA\\Results\\Figures/")

options(scipen = 999)

#### Libraries Needed -----------------------------------------------------------

## SDAD library (data linkage)
library(dplyr)
library(DBI)
library(ROracle)
library(ggplot2)
library(psych) # describe function
library(pastecs)
library(nFactors)
library(lavaan)
library(ggpubr)
library(sf) # Geospatial
library(tigris) # Geospatial
library(noncensus)
library(leaflet)
library(zipcode)
library(geojsonio)
library(htmltools)

#### Functions -----------------------------------------------------------

# Function to calculate D'Agostino-Pearson K^2 Test for Normality  
K2 <- function(x)
{
  # D'Agostino-Pearson K^2 Test for Normality
  # American Statistician 1990, vol. 44, No. 4, 316-321
  # Check to see if x is numeric and treat it as a vector 
  if(mode(x) != "numeric") stop("need numeric data")
  x <- as.vector(x)	#Remove any NA's
  x <- x[!is.na(x)]
  
  n <- length(x)	# Object for calculating the central moments
  centralmoment <- function(x, k)
  {
    sum((x - mean(x))^k)/length(x)
  }
  #Compute coefficient of skewness
  sqrt.b.1 <- centralmoment(x, 3)/centralmoment(x, 2)^(3/2)	
  # Compute coefficient of kurtosis
  b.2 <- centralmoment(x, 4)/centralmoment(x, 2)^2	
  # Test of Skewness
  y <- sqrt.b.1 * sqrt(((n + 1) * (n + 3))/(6 * (n - 2)))
  B.2.sqrt.b.1 <- (3 * (n^2 + 27 * n - 70) * (n + 1) * (n + 3))/((n - 2) * (n + 5) * (n + 7) * (n + 9))
  W2 <- -1 + sqrt(2 * (B.2.sqrt.b.1 - 1))
  W <- sqrt(W2)
  delta <- 1/sqrt(log(W))
  alpha <- sqrt(2/(W2 - 1))
  Z.sqrt.b.1 <- delta * log(y/alpha + sqrt((y/alpha)^2 + 1))	
  #Normal approximation
  prob.skewness <- (1 - pnorm(abs(Z.sqrt.b.1), 0, 1)) 	
  #Test of Kurtosis
  #Compute the mean of b_2
  exp.b.2 <- (3 * (n - 1))/(n + 1)	#Compute the variance of b.2
  var.b.2 <- (24 * n * (n - 2) * (n - 3))/((n + 1)^2 * (n + 3) * (n + 5))	
  # Compute the standardized version of b.2
  std.b.2 <- (b.2 - exp.b.2)/sqrt(var.b.2)	
  # Compute the third standardized moment of b.2
  sqrt.B.1.b.2 <- ((6 * (n^2 - 5 * n + 2))/((n + 7) * (n + 9))) * sqrt((6 * (n + 3) * (n + 5))/(n * (n - 2) * (n - 3)))
  A <- 6 + (8/sqrt.B.1.b.2) * (2/sqrt.B.1.b.2 + sqrt((1 + 4/(sqrt.B.1.b.2^2))))
  Z.b.2 <- ((1 - 2/(9 * A)) - ((1 - 2/A)/(1 + std.b.2 * sqrt(2/(A - 4))))^(1/3))/(sqrt(2/(9 * A)))	# Normal approximation
  prob.kurtosis <- (1 - pnorm(abs(Z.b.2), 0, 1))	
  # Omnibus K2 Test of Normality (Skewness/Kurtosis) 
  K2 <- Z.sqrt.b.1^2 + Z.b.2^2
  prob.K2 <- 1 - pchisq(K2, 2)
  ret.val <- c("skewness" = sqrt.b.1, 
               "Normal Approx. for Skewness" = Z.sqrt.b.1, 
               "Prob(Normal Approx. for Skewness)" = prob.skewness, 
               "kurtosis" = b.2, "Normal Approx. for Kurtosis" = 
                 Z.b.2, "Prob(Normal Approx. for Kurtosis)" = prob.kurtosis, normtest.K2 = K2, 
               "prob.K2" = prob.K2)
  return(ret.val)
}

# Function to calculate frequencies by year
freq.yr <- function(x) {
  # Soldier branch (Army, AF, Navy, CG, Marines)
  f_O_1 <- tibble::rownames_to_column(questionr::freq(x$SERVICE, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Branch") %>% dplyr::select(var, everything())
  # Soldier component (Active, Reserve, Guard)
  f_O_2 <- tibble::rownames_to_column(questionr::freq(x$COMPO, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Compo") %>% dplyr::select(var, everything())
  # Soldier MOS type
  f_O_3 <- tibble::rownames_to_column(questionr::freq(x$CAR_DIV, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "MOS Type") %>% dplyr::select(var, everything())
  # Soldier rank (start)
  f_O_4 <- tibble::rownames_to_column(questionr::freq(x$RANK_PDE, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Rank (Start)") %>% dplyr::select(var, everything())
  # Soldier rank (end)
  f_O_4b <- tibble::rownames_to_column(questionr::freq(x$RANK_PDE_last, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Rank (End)") %>% dplyr::select(var, everything())
  # Soldier MOS
  f_O_5 <- tibble::rownames_to_column(questionr::freq(x$MOS, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "MOS") %>% dplyr::select(var, everything())
  # Soldier MOS (redux)
  f_O_6 <- tibble::rownames_to_column(questionr::freq(x$MOS2, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "MOS (Redux)") %>% dplyr::select(var, everything())
  # Soldier prior service
  f_O_7 <- tibble::rownames_to_column(questionr::freq(x$PS, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Prior Service") %>% dplyr::select(var, everything())
  # Soldier year accession
  f_O_8 <- tibble::rownames_to_column(questionr::freq(x$YEAR_ACC, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Accession Year") %>% dplyr::select(var, everything())
  # Type of discharge
  f_O_9 <- tibble::rownames_to_column(questionr::freq(x$CHAR_SVC_CD, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Discharge Type") %>% dplyr::select(var, everything())
  # Type of discharge2
  f_O_10 <- tibble::rownames_to_column(questionr::freq(x$CHAR_SVC_CD2, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Discharge Type (Redux)") %>% dplyr::select(var, everything())
  # Court Martial Count
  f_O_11 <- tibble::rownames_to_column(questionr::freq(x$COURT_MARTIAL, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Court Martial") %>% dplyr::select(var, everything())
  # Letter of Reprimand Count
  f_O_12 <- tibble::rownames_to_column(questionr::freq(x$LETTER_REPRIMAND, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "LoR") %>% dplyr::select(var, everything())
  # Article 15 Count
  f_O_13 <- tibble::rownames_to_column(questionr::freq(x$ARTICLE15, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Article 15") %>% dplyr::select(var, everything())
  # Bad Papers Overall (combined count of CM, LoR, A15)
  f_O_14 <- tibble::rownames_to_column(questionr::freq(x$badpaper.overall, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Overall Bad Papers") %>% dplyr::select(var, everything())
  # Soldier age at accession
  f_O_15 <- tibble::rownames_to_column(questionr::freq(as.integer(x$AGE_ACC), digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Age at Accession") %>% dplyr::select(var, everything())
  # Soldier sex at accession
  f_O_16 <- tibble::rownames_to_column(questionr::freq(x$GENDER, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Sex") %>% dplyr::select(var, everything())
  # Soldier race at accession
  f_O_17 <- tibble::rownames_to_column(questionr::freq(x$M_RACE1, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Race") %>% dplyr::select(var, everything())
  # Soldier highest level education (start)
  f_O_18 <- tibble::rownames_to_column(questionr::freq(x$EDU_LVL_CD, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (Start)") %>% dplyr::select(var, everything())
  # Soldier highest level education (end)
  f_O_18b <- tibble::rownames_to_column(questionr::freq(x$EDU_LVL_CD_last, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (End)") %>% dplyr::select(var, everything())
  # Soldier highest level education (redux-start)
  f_O_19 <- tibble::rownames_to_column(questionr::freq(x$EDU_LVL_RE, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (Redux-Start)") %>% dplyr::select(var, everything())
  # Soldier highest level education (redux-end)
  f_O_19b <- tibble::rownames_to_column(questionr::freq(x$EDU_LVL_RE_last, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (Redux-End)") %>% dplyr::select(var, everything())
  # Soldier marital status (start)
  f_O_20 <- tibble::rownames_to_column(questionr::freq(x$MRTL_STAT_CD, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (Redux-Start)") %>% dplyr::select(var, everything())
  # Soldier marital status (end)
  f_O_20b <- tibble::rownames_to_column(questionr::freq(x$MRTL_STAT_CD_last, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (Redux-End)") %>% dplyr::select(var, everything())
  
  freq_O_c <- rbind(f_O_1, f_O_2, f_O_3, f_O_4, f_O_4b, f_O_5, f_O_6, f_O_7, f_O_8, f_O_9, f_O_10, f_O_11, f_O_12, f_O_13, f_O_14, f_O_15, f_O_16, f_O_17, f_O_18, f_O_18b, f_O_19, f_O_19b, f_O_20, f_O_20b)
  return(freq_O_c)
}

# Function for descriptive statistics
desc.yr <- function (x) {
  # Subset only numerical variables
  data.desc <- x %>% subset(select = c(AGE_ACC, AFQT_PCTL.CB, HEIGHT.CB, WEIGHT.CB, COURT_MARTIAL, LETTER_REPRIMAND, ARTICLE15, badpaper.overall, award_count, PULHES.TOTAL, PULHES.MEAN, BMI, APFT_1stSCORE, TFSES_HOLLHEAD, BFPCT_1stSCORE))
  
  # Descriptive stats table for variables in data frame
  dat <- pastecs::stat.desc(data.desc, norm = FALSE, p = .95)
  
  # Count unique values by variable and add new row
  dat2 <- data.desc %>% summarize_at(vars(everything()), n_distinct, na.rm = TRUE)
  dat2 <- as.data.frame(dat2)
  row.names(dat2) <- "val.unique"
  dat3 <- round(rbind(dat, dat2), 4) # Combine to add new column to descriptive table
  
  # Calculate D'Agostino-Pearson K^2 Test for Normality 
  dat4 <- as.data.frame(data.desc) %>% sapply(K2)
  dat4 <- round(dat4[c("skewness", "kurtosis", "normtest.K2", "prob.K2"),], 4)
  dat5 <- rbind(dat3, dat4) # Combine to add new column to descriptive table
  dat5 <- as.data.frame(t(as.matrix(dat5))) # transpose data frame from rows to columns
  dat5 <- dat5 %>% tibble::rownames_to_column() %>% mutate(pct.na = (nbr.na)/(nbr.na + nbr.val)) 
  dat5 <- dat5 %>% dplyr::select(rowname, nbr.val, nbr.null, nbr.na, pct.na, val.unique, min, max, range, sum, median, mean, SE.mean, CI.mean.0.95, std.dev, var,
                                 coef.var, skewness, kurtosis, normtest.K2, prob.K2) # Reorder columns
  return(dat5)
}




#### Data Linkage -----------------------------------------------------------

schema_name <- "STUDY_SDAL"

table_master <- "MV_MASTER_AD_ARMY_QTR_V3A"
table_mepcom <- "MEPCOM_USAREC_RA_ANALYST"
table_mepcom2 <- "MV_DMDC_MEPCOM_700_V2"
table_IPERMS <- "TA_IPERMS_DEROG_V2"
table_awards <- "MV_AWTF_AWARDS"
table_transaction <- "MV_TRANS_AD_ARMY_30_V3A"

# ---
## read in the initial variables to link
# ---

master_vars <- dbGetQuery(con, paste0("select PID_PDE, FILE_DT, DATE_BIRTH_PDE, PN_SEX_CD, RACE_CD, FAITH_GRP_CD, MRTL_STAT_CD, EDU_LVL_CD, HOR_US_ST_CD, PN_MA_US_ST_CNTY_CD, ZIP_CODE_PDE_PN_MA,
                                      AFQT_PCTL_SCR_QY, USVC_INIT_ENT_DT, SERVICE, COMPO, RANK_PDE, PAYGRADE_PDE, PRI_SVC_OCC_CD, DTY_BASE_FAC_ID, ASG_BASE_FAC_ID, STR_ACCT_CD 
                                      from ", schema_name, " . ", table_master))


mepcom_vars <- dbGetQuery(con, paste0("select PID_PDE, DATE_BIRTH, RELIGION, MARITAL, HEIGHT, WEIGHT, PULHES, STATE, CITY, ZIP_CODE_PDE, 
                                      AFQT, DATE_ACC, CAR_DIV, MOS, PS from ", schema_name, " . ", table_mepcom))


mepcom_vars2 <- dbGetQuery(con, paste0("select PID_PDE, SNPSHT_DT, DATE_BIRTH, PN_FAITH_GRP_CD, PN_MA_US_ST_CD, PN_MA_CTY_NM, PN_MRTL_STAT_CD, HGT_DM, PN_WGHT_QY, PHY_CPCY_PHY_PRFL_MOD_CD, 
                                      UXTR_PHY_PRFL_MOD_CD, LXTR_PHY_PRFL_MOD_CD, HRG_PHY_PRFL_MOD_CD, VSN_PHY_PRFL_MOD_CD, PSYC_PHY_PRFL_MOD_CD, AFQT_PCTL_SCR_QY, APLNT_USVC_AGMT_APP_DT,
                                      ACC_PRI_SVC_OCC_CD, MEP_PRIOR_SVC_IND_CD from ", schema_name, " . ", table_mepcom2))


IPERMS_vars <- dbGetQuery(con, paste0("select PID_PDE, DATE_DEROG_EFF, NAME_DEROG_DOC from ", schema_name, " . ", table_IPERMS))


awards_vars <- dbGetQuery(con, paste0("select PID_PDE, AWRD_DT, AWRD_CD from ", schema_name, " . ", table_awards))


transaction_vars <- dbGetQuery(con, paste0("select PID_PDE, AFMS_BASE_DT, TXN_EFF_DT, CHAR_SVC_CD, ADSVC_PE_DT, ENL_ASVC_OBLG_END_DT,
                                           ADP_TXN_TYP_CD, ISVC_SEP_CD from ", schema_name, " . ", table_transaction))

#sum(is.na(master_vars$EDU_LVL_CD))/length(master_vars$PID_PDE)
#sum(is.na(transaction_vars$AFMS_BASE_DT))/length(transaction_vars$PID_PDE)


# ---
## clean master file
# ---

# Set Accession date range (using 1st file date as proxy for accession year)
master_filter <- master_vars %>% dplyr::filter(FILE_DT >= as.POSIXct("2000-01-01"), FILE_DT <= as.POSIXct("2020-01-01")) 
remove(master_vars)

length(unique(master_filter$PID_PDE)) # 1,866,257

# filter Active Duty (service = A), Army (compo = A)
table(master_filter$SERVICE, useNA = "always") # A = 39,195,587 rows
table(master_filter$COMPO, useNA = "always") # G = 12,859, R = 38,009,041, V = 1,162,979, NA = 10,708 rows

# Filter active duty only (R)
master_filter2 <- master_filter %>% dplyr::filter(COMPO == "R") # 38,009,041 rows
remove(master_filter)

# Slice first record
master_reduced.A <- master_filter2 %>% dplyr::group_by(PID_PDE) %>% dplyr::filter(FILE_DT == min(FILE_DT)) %>% dplyr::ungroup()
# Slice last record
master_reduced.O <- master_filter2 %>% dplyr::group_by(PID_PDE) %>% dplyr::filter(FILE_DT == max(FILE_DT)) %>% dplyr::ungroup() 
remove(master_filter2)

table(master_reduced.A$RANK_PDE, useNA = "always")
#  1LT    2LT    CPL    CPT    CW2    CW3    EEE    MAJ    OOO    PFC    PV1    PV2    SFC    SGT    SSG    WO1    WWW   <NA> 
# 10973  57077 222143  37615   2563   6377  14587  21247  14061 275818 649167 348908  37224  84361  58179     43   2019     30 
table(master_reduced.O$RANK_PDE, useNA = "always")
#  1LT    2LT    CPL    CPT    CW2    CW3    EEE    MAJ    OOO    PFC    PV1    PV2    SFC    SGT    SSG    WO1    WWW   <NA> 
# 20841   9259 569741  63669   8701  10228  58275  31547  45557 172519 172901 127620 112530 284181 144031     52  10809     12 

master_reduced.O <- master_reduced.O %>% dplyr::rename(RANK_PDE_last = RANK_PDE, FILE_DT_last = FILE_DT, PAYGRADE_PDE_last = PAYGRADE_PDE, 
                                                       EDU_LVL_CD_last = EDU_LVL_CD, MRTL_STAT_CD_last = MRTL_STAT_CD)
master_reduced.O <- master_reduced.O %>% dplyr::select(PID_PDE, RANK_PDE_last, FILE_DT_last, PAYGRADE_PDE_last, EDU_LVL_CD_last, MRTL_STAT_CD_last)

master_reduced.AO <- master_reduced.A %>% dplyr::left_join(master_reduced.O, by = "PID_PDE")
remove(master_reduced.A, master_reduced.O)

# ---
## join mepcom
# ---

# join by PID
# Keep only unique cases for mep1 and use the latest date on the SNPSHT_DT var for mep2 as it provides most complete data for each case
mep1 <- mepcom_vars %>% dplyr::distinct(PID_PDE, .keep_all = TRUE)
remove(mepcom_vars)
mep2 <- mepcom_vars2 %>% dplyr::group_by(PID_PDE) %>% dplyr::filter(SNPSHT_DT == max(SNPSHT_DT)) %>% dplyr::ungroup() 
remove(mepcom_vars2)

# join both mepcom data tables (.x vars = mep1 of same name as mep2 vars which are .y)
linkdat1a <- master_reduced.AO %>% dplyr::left_join(mep1, by = "PID_PDE")
linkdat1b <- linkdat1a %>% dplyr::left_join(mep2, by = "PID_PDE")
remove(master_reduced.AO, mep1, mep2, linkdat1a)

# ---
# join IPERMS
# ---

# counts of Court Martial, Article 15, Letter of Reprimand
IPERMS_counts <- IPERMS_vars %>% group_by(PID_PDE) %>% summarize(COURT_MARTIAL = sum(NAME_DEROG_DOC == "COURT MART"),
                                                                 LETTER_REPRIMAND = sum(NAME_DEROG_DOC == "LTR REPR"),
                                                                 ARTICLE15 = sum(NAME_DEROG_DOC == "DA 2627")) %>% ungroup()

# join counts by PID_PDE
linkdat2 <- linkdat1b %>% left_join(IPERMS_counts, by = "PID_PDE")
remove(linkdat1b, IPERMS_counts, IPERMS_vars)

# set counts to 0 if none observed (NA)
linkdat2$COURT_MARTIAL[is.na(linkdat2$COURT_MARTIAL)] <- 0
linkdat2$LETTER_REPRIMAND[is.na(linkdat2$LETTER_REPRIMAND)] <- 0
linkdat2$ARTICLE15[is.na(linkdat2$ARTICLE15)] <- 0


# ---
# join AWARD counts
# ---

award_count <- awards_vars %>% group_by(PID_PDE) %>% summarise(award_count = n()) %>% ungroup()

linkdat3 <- linkdat2 %>% left_join(award_count, by = "PID_PDE")
remove(linkdat2, award_count, awards_vars)

# set counts to 0 if none observed (NA)
linkdat3$award_count[is.na(linkdat3$award_count)] <- 0
linkdat3$award_count <- as.integer(linkdat3$award_count)

# ---
# join Transaction variables
# ---

last_transaction <- transaction_vars %>% group_by(PID_PDE) %>% arrange(desc(TXN_EFF_DT)) %>% slice(1)

linkdat4 <- linkdat3 %>% left_join(last_transaction, by = "PID_PDE")


table(linkdat4$RANK_PDE, useNA = "always") # 1,842,817 Cases
#   1LT    2LT    CPL    CPT    CW2    CW3    EEE    MAJ    OOO    PFC    PV1    PV2    SFC    SGT    SSG    WO1    WWW   <NA> 
#  10973  57077 222143  37700   2563   6377  14587  21247  14061 275903 649337 348908  37309  84361  58179     43   2019     30 

#fwrite(linkdat4, file = "performance/Army20Yr_linked_data.csv", row.names = F)


### Calc first APFT Score ########
schema_name <- "STUDY_SDAL"
table_APFT <- "TA_DTMS_APFT"
APFT_vars <- dbGetQuery(con, paste0("select PID_PDE, DATE_APFT, ALT_EVENT, ALT_EVENT_GO, APFT_PASS, SCORE_TOTAL,
                                    EXEMPT_PUSHUP, EXEMPT_SITUP from ", schema_name, " . ", table_APFT))
length(unique(APFT_vars$PID_PDE)) # N = 1,487,794
apft1 <- APFT_vars %>% group_by(PID_PDE) %>% arrange(DATE_APFT) %>% slice(1) %>% dplyr::select(PID_PDE, SCORE_TOTAL)
apft1$APFT_1stSCORE <- apft1$SCORE_TOTAL
#tt <- data %>% filter(is.na(APFT_1stSCORE)) %>% select(PID_PDE, RANK_PDE_GRP, YEAR_ACC.CB, APFT_1stSCORE)
#APFT_vars %>% dplyr::filter(PID_PDE == "PDE1JMBTZK7C")
#tt %>% group_by(YEAR_ACC.CB) %>% summarise(n = n()) # inconsistent reporting before 2007, no records after JUN 2016

#apft1
#APFT_vars %>% dplyr::filter(PID_PDE == "PDE0004AEANH")
apft1 <- apft1 %>% dplyr::select(PID_PDE, APFT_1stSCORE)
length(unique(apft1$PID_PDE)) # N = 1,487,794
# join
data <- data %>% left_join(apft1, by = "PID_PDE")
names(data)

#data.table::fwrite(data, file = "performance/Army20Yr_linked_data_analytics.csv", row.names = F) # save recoded and new variable file


### Calc career APFT Score & BMI ########
# APFT
schema_name <- "STUDY_SDAL"
table_APFT <- "TA_DTMS_APFT"
APFT_vars <- dbGetQuery(con, paste0("select PID_PDE, DATE_APFT, SCORE_TOTAL from ", schema_name, " . ", table_APFT))

# APFT taken twice a year; for someone acceessing in 2000, a possible of # of 40 tests
#a <- APFT_vars %>% group_by(PID_PDE) %>% dplyr::summarise(n = n())
#max(a$n, na.rm = TRUE) # 97
#mean(a$n, na.rm = TRUE) # 5.21
#sd(a$n, na.rm = TRUE) # 4.36
#APFT_vars %>% dplyr::filter(PID_PDE == "PDE0004AEANH")
APFT_vars2 <- APFT_vars %>% group_by(PID_PDE) %>% dplyr::arrange(DATE_APFT) %>% dplyr::slice(1:40) %>% dplyr::ungroup()
length(unique(APFT_vars2$PID_PDE)) # 1,487,794
APFT_vars2 <- APFT_vars2 %>% group_by(PID_PDE) %>% dplyr::mutate(testno = row_number()) %>% dplyr::ungroup()
# cast to wide format by PID
# naming convention for first instance ".1", second ".2"; NA if less than five observed
APFT_vars3 <- reshape(as.data.frame(APFT_vars2), idvar = "PID_PDE", timevar = "testno", direction = "wide")
length(unique(APFT_vars3$PID_PDE)) # 1,487,794
APFT_vars3 %>% dplyr::filter(PID_PDE == "PDE0004AEANH")
APFT_vars4 <- APFT_vars3 %>% filter(PID_PDE %in% data$PID_PDE)
length(unique(APFT_vars4$PID_PDE)) # 713,272

apft.rm <- APFT_vars4 %>% dplyr::select(starts_with("SCORE_TOTAL"))
apft.rm2 <- pastecs::stat.desc(apft.rm, norm = FALSE, p = .95)
apft.rm2 <- as.data.frame(t(as.matrix(apft.rm2))) # transpose data frame from rows to columns
#write.csv(apft.rm2, "\\\\facaa7pde01p\\PDE\\Projects\\ARI\\ARI-SDAL\\analysis\\ratcliff\\ARI2\\ArmyChrYr\\Army20Yr\\Results\\Figures\\Army20Yr_APFT_repmeans.csv") # save output
#data.table::fwrite(APFT_vars4, file = "\\\\facaa7pde01p\\PDE\\Projects\\ARI\\ARI-SDAL\\analysis\\ratcliff\\ARI2\\ArmyChrYr\\Army20Yr\\Army20Yr_APFT_repeated.csv", row.names = F) # save recoded and new variable file

# bring in sex
names(APFT_vars4)
APFT.rm2 <- APFT_vars4 %>% dplyr::select(starts_with("PID"), starts_with("SCORE_TOTAL"))
APFT.rm2 <- APFT.rm2 %>% dplyr::left_join(data %>% dplyr::filter(PN_SEX_CD == "male" | PN_SEX_CD == "female") %>% dplyr::select(PID_PDE, PN_SEX_CD), by = "PID_PDE")
names(APFT.rm2)
APFT.rm2m <- APFT.rm2 %>% dplyr::filter(PN_SEX_CD == "male")
APFT.rm2m <- APFT.rm2m %>% dplyr::select(-PID_PDE, -PN_SEX_CD)
APFT.rm2f <- APFT.rm2 %>% dplyr::filter(PN_SEX_CD == "female") 
APFT.rm2f <- APFT.rm2f %>% dplyr::select(-PID_PDE, -PN_SEX_CD)
resultsm <- pastecs::stat.desc(APFT.rm2m, norm = FALSE, p = .95)
resultsm <- tibble::rownames_to_column(as.data.frame(t(as.matrix(resultsm)))) %>% dplyr::mutate(sex = "Male") # transpose data frame from rows to columns
resultsf <- pastecs::stat.desc(APFT.rm2f, norm = FALSE, p = .95)
resultsf <- tibble::rownames_to_column(as.data.frame(t(as.matrix(resultsf)))) %>% dplyr::mutate(sex = "Female") # transpose data frame from rows to columns
results_c <- rbind(resultsm, resultsf)
results_c <- results_c %>% dplyr::select(sex, everything())
write.csv(results_c, "ARMY20Yr_APFTbySEX_repmeans.csv")

## Single variable (wide format) RM-ANOVA (1st 10 time points ~ 5 years)
apft_rm.model <- lm(cbind(apft.rm$SCORE_TOTAL.1, apft.rm$SCORE_TOTAL.2, apft.rm$SCORE_TOTAL.3, apft.rm$SCORE_TOTAL.4, apft.rm$SCORE_TOTAL.5, apft.rm$SCORE_TOTAL.6, apft.rm$SCORE_TOTAL.7, 
                          apft.rm$SCORE_TOTAL.8, apft.rm$SCORE_TOTAL.9, apft.rm$SCORE_TOTAL.10) ~ 1)
trial1 <- factor(c('Time 1', 'Time 2', 'Time 3', ' Time 4', 'Time 5', 'Time 6', 'Time 7', 'Time 8', ' Time 9', 'Time 10'), ordered = FALSE)
rANOVA1 <- car::Anova(apft_rm.model, idata = data.frame(trial1), idesign = ~ trial1, type = 'III', digits = 4)
rANOVA1 <- summary(rANOVA1, multivariate = FALSE)
x1 <- rANOVA1$univariate.tests %>% as.matrix() %>% unclass() %>% as.data.frame()
x2 <- rANOVA1$pval.adjustments %>% as.matrix() %>% unclass() %>% as.data.frame()
x3 <- rANOVA1$sphericity.tests %>% as.matrix() %>% unclass() %>% as.data.frame()
a4 <- cbind(x1, x2, x3)
ges.ci <- MOTE::ges.partial.SS.mix(dfm = a4[2,2], dfe = a4[2,4], ssm = a4[2,1], sss = a4[1,3], sse = a4[2,3], Fvalue = a4[2,5], a = 0.10)
rANOVA1 <- a4 %>% mutate(ges = ges.ci$ges, ci.lower = ges.ci$geslow, ci.upper = ges.ci$geshigh)
#write.csv(rANOVA1, "\\\\facaa7pde01p\\PDE\\Projects\\ARI\\ARI-SDAL\\analysis\\ratcliff\\ARI2\\ArmyChrYr\\Army20Yr\\Results\\Figures\\Army20Yr_APFT_rmANOVA(1st10).csv") # save output

## Single variable (wide format) RM-ANOVA (1st 20 time points ~ 10 years)
apft_rm.model2 <- lm(cbind(apft.rm$SCORE_TOTAL.1, apft.rm$SCORE_TOTAL.2, apft.rm$SCORE_TOTAL.3, apft.rm$SCORE_TOTAL.4, apft.rm$SCORE_TOTAL.5, apft.rm$SCORE_TOTAL.6, apft.rm$SCORE_TOTAL.7, 
                           apft.rm$SCORE_TOTAL.8, apft.rm$SCORE_TOTAL.9, apft.rm$SCORE_TOTAL.10, apft.rm$SCORE_TOTAL.11, apft.rm$SCORE_TOTAL.12, apft.rm$SCORE_TOTAL.13, apft.rm$SCORE_TOTAL.14, 
                           apft.rm$SCORE_TOTAL.15, apft.rm$SCORE_TOTAL.16, apft.rm$SCORE_TOTAL.17,  apft.rm$SCORE_TOTAL.18, apft.rm$SCORE_TOTAL.19, apft.rm$SCORE_TOTAL.20) ~ 1)
trial2 <- factor(c('Time 1', 'Time 2', 'Time 3', ' Time 4', 'Time 5', 'Time 6', 'Time 7', 'Time 8', ' Time 9', 'Time 10', 
                   'Time 11', 'Time 12', 'Time 13', ' Time 14', 'Time 15', 'Time 16', 'Time 17', 'Time 18', ' Time 19', 'Time 20'), ordered = FALSE)
rANOVA2 <- car::Anova(apft_rm.model2, idata = data.frame(trial2), idesign = ~ trial2, type = 'III', digits = 4)
rANOVA2 <- summary(rANOVA2, multivariate = FALSE)
x1 <- rANOVA2$univariate.tests %>% as.matrix() %>% unclass() %>% as.data.frame()
x2 <- rANOVA2$pval.adjustments %>% as.matrix() %>% unclass() %>% as.data.frame()
x3 <- rANOVA2$sphericity.tests %>% as.matrix() %>% unclass() %>% as.data.frame()
a4 <- cbind(x1, x2, x3)
ges.ci <- MOTE::ges.partial.SS.mix(dfm = a4[2,2], dfe = a4[2,4], ssm = a4[2,1], sss = a4[1,3], sse = a4[2,3], Fvalue = a4[2,5], a = 0.10)
rANOVA2 <- a4 %>% mutate(ges = ges.ci$ges, ci.lower = ges.ci$geslow, ci.upper = ges.ci$geshigh)
#write.csv(rANOVA2, "\\\\facaa7pde01p\\PDE\\Projects\\ARI\\ARI-SDAL\\analysis\\ratcliff\\ARI2\\ArmyChrYr\\Army20Yr\\Results\\Figures\\Army20Yr_APFT_rmANOVA(1st20).csv") # save output

# First Body Fat %
schema_name <- "STUDY_SDAL"
table_HT_WT <- "TA_DTMS_HT_WT"
HT_WT_vars <- dbGetQuery(con, paste0("select PID_PDE, DATE_BODYCOMP, HEIGHT, WEIGHT, BODYFAT_PERCENT from ", schema_name, " . ", table_HT_WT))
length(unique(HT_WT_vars$PID_PDE)) # N = 1,146,096
bfpct1 <- HT_WT_vars %>% group_by(PID_PDE) %>% arrange(DATE_BODYCOMP) %>% slice(1) %>% dplyr::select(PID_PDE, BODYFAT_PERCENT)
bfpct1$BFPCT_1stSCORE <- bfpct1$BODYFAT_PERCENT
bfpct1 <- bfpct1 %>% dplyr::select(PID_PDE, BFPCT_1stSCORE)
length(unique(bfpct1$PID_PDE)) # N = 1,146,096
# join
data <- data %>% left_join(bfpct1, by = "PID_PDE")
names(data)
sum(is.na(data$BFPCT_1stSCORE))/length(data$PID_PDE)*100 # 86.18%
#data.table::fwrite(data, file = "performance/Army20Yr_linked_data_analytics.csv", row.names = F) # save recoded and new variable file

# BMI
schema_name <- "STUDY_SDAL"
table_HT_WT <- "TA_DTMS_HT_WT"
HT_WT_vars <- dbGetQuery(con, paste0("select PID_PDE, DATE_BODYCOMP, HEIGHT, WEIGHT, BODYFAT_PERCENT from ", schema_name, " . ", table_HT_WT))

# HT/WT taken twice a year; for someone acceessing in 2000, a possible of # of 40 tests
a <- HT_WT_vars %>% group_by(PID_PDE) %>% dplyr::summarise(n = n())
max(a$n, na.rm = TRUE) # 71
mean(a$n, na.rm = TRUE) # 3.99
sd(a$n, na.rm = TRUE) # 3.33
HT_WT_vars %>% dplyr::filter(PID_PDE == "PDE0004AEANH")
HT_WT_vars$BMI <- ((HT_WT_vars$WEIGHT * 703) / ((HT_WT_vars$HEIGHT)^2))

HT_WT_vars2 <- HT_WT_vars %>% group_by(PID_PDE) %>% dplyr::arrange(DATE_BODYCOMP) %>% dplyr::slice(1:40) %>% dplyr::ungroup()
length(unique(HT_WT_vars2$PID_PDE)) # 1,146,096
HT_WT_vars2 <- HT_WT_vars2 %>% dplyr::filter(BMI < 42.92, BMI > 6.26)
length(unique(HT_WT_vars2$PID_PDE)) # 1,143,475
HT_WT_vars2 <- HT_WT_vars2 %>% group_by(PID_PDE) %>% dplyr::mutate(testno = row_number()) %>% dplyr::ungroup()
# cast to wide format by PID
# naming convention for first instance ".1", second ".2"; NA if less than five observed
HT_WT_vars3 <- reshape(as.data.frame(HT_WT_vars2), idvar = "PID_PDE", timevar = "testno", direction = "wide")
length(unique(HT_WT_vars3$PID_PDE)) # 1,143,475
HT_WT_vars3 %>% dplyr::filter(PID_PDE == "PDE0004AEANH")
HT_WT_vars4 <- HT_WT_vars3 %>% filter(PID_PDE %in% data$PID_PDE)
length(unique(HT_WT_vars4$PID_PDE)) # 526,096

HTWT.rm <- HT_WT_vars4 %>% dplyr::select(starts_with("BMI"), starts_with("BODYFAT"))
HTWT.rm$BMI.1[!is.finite(HTWT.rm$BMI.1)] <- NA
HTWT.rm2 <- pastecs::stat.desc(HTWT.rm, norm = FALSE, p = .95)
HTWT.rm2 <- as.data.frame(t(as.matrix(HTWT.rm2))) # transpose data frame from rows to columns
write.csv(HTWT.rm2, "\\\\facaa7pde01p\\PDE\\Projects\\ARI\\ARI-SDAL\\analysis\\ratcliff\\ARI2\\ArmyChrYr\\Army20Yr\\Results\\Figures\\Army20Yr_HTWT_repmeans(outlier_removal).csv") # save output
data.table::fwrite(HT_WT_vars4, file = "\\\\facaa7pde01p\\PDE\\Projects\\ARI\\ARI-SDAL\\analysis\\ratcliff\\ARI2\\ArmyChrYr\\Army20Yr\\Army20Yr_HTWT_repeated(outlier_removal).csv", row.names = F) # save recoded and new variable file

# bring in sex
names(HT_WT_vars4)
HTWT.rm2 <- HT_WT_vars4 %>% dplyr::select(starts_with("PID"), starts_with("BODYFAT"))
HTWT.rm2 <- HTWT.rm2 %>% dplyr::left_join(data %>% dplyr::filter(PN_SEX_CD == "male" | PN_SEX_CD == "female") %>% dplyr::select(PID_PDE, PN_SEX_CD), by = "PID_PDE")
names(HTWT.rm2)
HTWT.rm2m <- HTWT.rm2 %>% dplyr::filter(PN_SEX_CD == "male")
HTWT.rm2m <- HTWT.rm2m %>% dplyr::select(-PID_PDE, -PN_SEX_CD)
HTWT.rm2f <- HTWT.rm2 %>% dplyr::filter(PN_SEX_CD == "female") 
HTWT.rm2f <- HTWT.rm2f %>% dplyr::select(-PID_PDE, -PN_SEX_CD)
resultsm <- pastecs::stat.desc(HTWT.rm2m, norm = FALSE, p = .95)
resultsm <- tibble::rownames_to_column(as.data.frame(t(as.matrix(resultsm)))) %>% dplyr::mutate(sex = "Male") # transpose data frame from rows to columns
resultsf <- pastecs::stat.desc(HTWT.rm2f, norm = FALSE, p = .95)
resultsf <- tibble::rownames_to_column(as.data.frame(t(as.matrix(resultsf)))) %>% dplyr::mutate(sex = "Female") # transpose data frame from rows to columns
results_c <- rbind(resultsm, resultsf)
results_c <- results_c %>% dplyr::select(sex, everything())
write.csv(results_c, "ARMY20Yr_BODYFATPCTbySEX_repmeans(outlier_removal).csv")

#END

### Calc first APFT Raw Event Scores ########
schema_name <- "STUDY_SDAL"
table_APFT <- "TA_DTMS_APFT"
APFT_vars <- dbGetQuery(con, paste0("select PID_PDE, DATE_APFT, RAW_PUSHUPS, RAW_SITUPS, RAW_RUN, SCORE_PUSHUP, SCORE_SITUP, SCORE_RUN, SCORE_TOTAL from ", schema_name, " . ", table_APFT))
length(unique(APFT_vars$PID_PDE)) # N = 1,487,794
apft1 <- APFT_vars %>% group_by(PID_PDE) %>% arrange(DATE_APFT) %>% slice(1) %>% dplyr::select(PID_PDE, RAW_PUSHUPS, RAW_SITUPS, RAW_RUN, SCORE_PUSHUP, SCORE_SITUP, SCORE_RUN, SCORE_TOTAL)
apft1$APFT_1stRAWPUSHUP <- apft1$RAW_PUSHUPS
apft1$APFT_1stRAWSITUP <- apft1$RAW_SITUPS
apft1$APFT_1stRAWRUN <- apft1$RAW_RUN

#apft1
apft1 <- apft1 %>% dplyr::select(PID_PDE, APFT_1stRAWPUSHUP, APFT_1stRAWSITUP, APFT_1stRAWRUN)
length(unique(apft1$PID_PDE)) # N = 1,487,794
# join
data <- data %>% left_join(apft1, by = "PID_PDE")
data$APFT_1stRAWRUN <- lubridate::ms(data$APFT_1stRAWRUN)
data$APFT_1stRAWRUN <- (lubridate::period_to_seconds(data$APFT_1stRAWRUN)/60)
## ERROR: Data for RAW_PUSHUPS (actually situps) and RAW_SITUPS (actually pushups) should be switched
#data %>% dplyr::select(PID_PDE, APFT_1stRAWPUSHUP, APFT_1stRAWSITUP)
data <- data %>% dplyr::rename(APFT_1stRAWSITUP = APFT_1stRAWPUSHUP, APFT_1stRAWPUSHUP = APFT_1stRAWSITUP)
names(data)
#data.table::fwrite(data, file = "performance/Army20Yr_linked_data_analytics.csv", row.names = F) # save recoded and new variable file


### Calc career APFT Raw Event Scores ########
schema_name <- "STUDY_SDAL"
table_APFT <- "TA_DTMS_APFT"
APFT_vars <- dbGetQuery(con, paste0("select PID_PDE, DATE_APFT, RAW_PUSHUPS, RAW_SITUPS, RAW_RUN, SCORE_PUSHUP, SCORE_SITUP, SCORE_RUN, SCORE_TOTAL from ", schema_name, " . ", table_APFT))
length(unique(APFT_vars$PID_PDE)) # N = 1,487,794
APFT_vars$RAW_RUN <- lubridate::ms(APFT_vars$RAW_RUN)
APFT_vars$RAW_RUN <- (lubridate::period_to_seconds(APFT_vars$RAW_RUN)/60)
head(APFT_vars)
#APFT_vars %>% filter(!is.na(RAW_RUN))
# create mean APFT variables across Soldier's career
APFT_vars <- APFT_vars %>% dplyr::group_by(PID_PDE) %>% dplyr::mutate(APFT_TOTALRAWPUSHUP = mean(RAW_PUSHUPS, na.rm = TRUE)) %>% dplyr::ungroup() %>% as.data.frame() # regular score
APFT_vars <- APFT_vars %>% dplyr::group_by(PID_PDE) %>% dplyr::mutate(APFT_TOTALRAWSITUP = mean(RAW_SITUPS, na.rm = TRUE)) %>% dplyr::ungroup() %>% as.data.frame() # regular score
APFT_vars <- APFT_vars %>% dplyr::group_by(PID_PDE) %>% dplyr::mutate(APFT_TOTALRAWRUN = mean(RAW_RUN, na.rm = TRUE)) %>% dplyr::ungroup() %>% as.data.frame() # regular score
APFT_vars <- APFT_vars %>% dplyr::group_by(PID_PDE) %>% dplyr::mutate(APFT_TOTALSCORE = mean(SCORE_TOTAL, na.rm = TRUE)) %>% dplyr::ungroup() %>% as.data.frame() # regular score

#APFT_vars %>% dplyr::filter(PID_PDE == "PDEP3RD2UQNO")
#head(APFT_vars)
# take the last observed APFT
APFT_JOIN <- APFT_vars %>% group_by(PID_PDE) %>% arrange(desc(DATE_APFT)) %>% slice(1) %>% dplyr::select(PID_PDE, APFT_TOTALRAWPUSHUP, APFT_TOTALRAWSITUP, APFT_TOTALRAWRUN, APFT_TOTALSCORE) %>% dplyr::ungroup() %>% as.data.frame()
#APFT_JOIN %>% dplyr::filter(PID_PDE == "PDEBQQJSKWSZ")
length(unique(APFT_JOIN$PID_PDE)) # N = 1,487,794
# join
data <- data %>% left_join(APFT_JOIN, by = "PID_PDE")
## ERROR: Data for RAW_PUSHUPS (actually situps) and RAW_SITUPS (actually pushups) should be switched
#data %>% dplyr::select(PID_PDE, APFT_TOTALRAWPUSHUP, APFT_TOTALRAWSITUP)
data <- data %>% dplyr::rename(APFT_TOTALRAWSITUP = APFT_TOTALRAWPUSHUP, APFT_TOTALRAWPUSHUP = APFT_TOTALRAWSITUP)
names(data)
#data.table::fwrite(data, file = "performance/Army20Yr_linked_data_analytics.csv", row.names = F) # save recoded and new variable file


#END
### Soldier Home County at Accession ######
## MEPCOM
mepcom_vars2 <- dbGetQuery(con, paste0("select PID_PDE, SNPSHT_DT, APLNT_HOR_US_ST_CD, APLNT_HOR_US_ST_CNTY_CD,
                                       PN_MA_US_ST_CD, PN_MA_US_ST_CNTY_CD, PN_MA_CTY_NM from ", schema_name, " . ", table_mepcom2))

names(data)
head(mepcom_vars2)
length(unique(mepcom_vars2$PID_PDE)) # 9,004,174
mepcom_vars2 <- mepcom_vars2 %>% dplyr::distinct(PID_PDE, .keep_all = TRUE)
length(unique(mepcom_vars2$PID_PDE)) # 9,004,174
# APLNT HOR appears to be the same to PN_MA vars
sum(is.na(mepcom_vars2$APLNT_HOR_US_ST_CD))/length(mepcom_vars2$PID_PDE)*100 # 0.05%
sum(is.na(mepcom_vars2$APLNT_HOR_US_ST_CNTY_CD))/length(mepcom_vars2$PID_PDE)*100 # 0.68%
sum(is.na(mepcom_vars2$PN_MA_US_ST_CD))/length(mepcom_vars2$PID_PDE)*100 # 0.00%
sum(is.na(mepcom_vars2$PN_MA_US_ST_CNTY_CD))/length(mepcom_vars2$PID_PDE)*100 # 0.49%
mepcom_vars2 %>% dplyr::filter(APLNT_HOR_US_ST_CD == "AL", APLNT_HOR_US_ST_CNTY_CD == "010") # not there
mepcom_vars2 %>% dplyr::filter(PN_MA_US_ST_CD == "AL", PN_MA_US_ST_CNTY_CD == "010") # non-valid combo present

# Recode alpha coded states to FIPS
sort(unique(mepcom_vars2$APLNT_HOR_US_ST_CD))
# JA = Jalisco, Mexico; WW = NA; SW = ?; UK = ?; GE = ?
mepcom_vars2$MEPSTATEFIPS <- dplyr::recode(mepcom_vars2$APLNT_HOR_US_ST_CD, AK = "02", AL = "01", AR = "05", AS = "60", AZ = "04", CA = "06", 
                                           CO = "08", CT = "09", DC = "11", DE = "10", FL = "12", FM = "64", GA = "13", GE = "", GU = "66", HI = "15", IA = "19", ID = "16", 
                                           IL = "17", IN = "18", JA = "", KS = "20", KY = "21", LA = "22", MA = "25", MD = "24", ME = "23", MH = "68", MI = "26", MN = "27", MO = "29", 
                                           MP = "69", MS = "28", MT = "30", NC = "37", ND = "38", NE = "31", NH = "33", NJ = "34", NM = "35", NV = "32", NY = "36", OH = "39", OK = "40", 
                                           OR = "41", PA = "42", PR = "72", PW = "70", RI = "44", SC = "45", SD = "46", SW = "", TN = "47", TX = "48", UK = "", UT = "49", VA = "51", 
                                           VI = "78", VT = "50", WA = "53", WI = "55", WV = "54", WW = "", WY = "56") 
mepcom_vars2$MEPSTATEFIPS[mepcom_vars2$MEPSTATEFIPS == ""] <- NA
# Combine state FIPS with county FIPS
mepcom_vars2$MEPCOUNTY3 <- mepcom_vars2$APLNT_HOR_US_ST_CNTY_CD
mepcom_vars2$MEPCOUNTY5 <- stringr::str_c(mepcom_vars2$MEPSTATEFIPS, mepcom_vars2$MEPCOUNTY3, sep = "")
mepcom_vars2$MEPSTATE <- mepcom_vars2$APLNT_HOR_US_ST_CD

mepcom_vars2 <- mepcom_vars2 %>% dplyr::select(PID_PDE, MEPSTATE, MEPSTATEFIPS, MEPCOUNTY3, MEPCOUNTY5)
data <- data %>% dplyr::left_join(mepcom_vars2, by = "PID_PDE")
sum(is.na(data$MEPCOUNTY5))/length(data$PID_PDE)*100 # 5.21%

## MASTER 
master_vars <- dbGetQuery(con, paste0("select PID_PDE, FILE_DT, HOR_US_ST_CD, PN_MA_US_ST_CD, PN_MA_US_ST_N_CD, PN_MA_US_ST_CNTY_CD from ", schema_name, " . ", table_master))
names(data)
head(master_vars)
master_vars <- master_vars %>% dplyr::group_by(PID_PDE) %>% dplyr::filter(FILE_DT == min(FILE_DT)) %>% dplyr::ungroup()
length(unique(master_vars$PID_PDE)) # 1,866,257
master_vars <- master_vars %>% dplyr::distinct(PID_PDE, .keep_all = TRUE)
length(unique(master_vars$PID_PDE)) # 1,866,257
# APLNT HOR appears to be the same to PN_MA vars
sum(is.na(master_vars$HOR_US_ST_CD))/length(master_vars$PID_PDE)*100 # 5.50%
sum(is.na(master_vars$PN_MA_US_ST_CD))/length(master_vars$PID_PDE)*100 # 6.25%
sum(is.na(master_vars$PN_MA_US_ST_N_CD))/length(master_vars$PID_PDE)*100 # 37.86%
sum(is.na(master_vars$PN_MA_US_ST_CNTY_CD))/length(master_vars$PID_PDE)*100 # 1.65%
master_vars %>% dplyr::filter(HOR_US_ST_CD == "AL", PN_MA_US_ST_CNTY_CD == "010") # 
master_vars %>% dplyr::filter(PN_MA_US_ST_CD == "AL", PN_MA_US_ST_CNTY_CD == "010") # 
# Recode alpha coded states to FIPS
sort(unique(master_vars$HOR_US_ST_CD))
# JA = Jalisco, Mexico; WW = NA; SW = ?; UK = ?; GE = ?
master_vars$MASTSTATEFIPS <- dplyr::recode(master_vars$HOR_US_ST_CD, AK = "02", AL = "01", AR = "05", AS = "60", AZ = "04", CA = "06", 
                                           CO = "08", CT = "09", DC = "11", DE = "10", FL = "12", FM = "64", GA = "13", GE = "", GU = "66", HI = "15", IA = "19", ID = "16", 
                                           IL = "17", IN = "18", JA = "", KS = "20", KY = "21", LA = "22", MA = "25", MD = "24", ME = "23", MH = "68", MI = "26", MN = "27", MO = "29", 
                                           MP = "69", MS = "28", MT = "30", NC = "37", ND = "38", NE = "31", NH = "33", NJ = "34", NM = "35", NV = "32", NY = "36", OH = "39", OK = "40", 
                                           OR = "41", PA = "42", PR = "72", PW = "70", RI = "44", SC = "45", SD = "46", SW = "", TN = "47", TX = "48", UK = "", UT = "49", VA = "51", 
                                           VI = "78", VT = "50", WA = "53", WI = "55", WV = "54", WW = "", WY = "56") 
master_vars$MASTSTATEFIPS[master_vars$MASTSTATEFIPS == ""] <- NA
# Combine state FIPS with county FIPS
master_vars$MASTCOUNTY3 <- master_vars$PN_MA_US_ST_CNTY_CD
master_vars$MASTCOUNTY3[master_vars$MASTCOUNTY3 == "999"] <- NA
master_vars$MASTCOUNTY5 <- stringr::str_c(master_vars$MASTSTATEFIPS, master_vars$MASTCOUNTY3, sep = "")
master_vars$MASTSTATE <- master_vars$HOR_US_ST_CD
sum(is.na(master_vars$MASTCOUNTY5))/length(master_vars$PID_PDE)*100 # 38.97%
master_vars <- master_vars %>% dplyr::select(PID_PDE, MASTSTATE, MASTSTATEFIPS, MASTCOUNTY3, MASTCOUNTY5)
data <- data %>% dplyr::left_join(master_vars, by = "PID_PDE")


# Coalesce
# fix paste error from combining number with NA
head(data)
names(data)
data$MEPSTATEFIPS <- stringr::str_pad(data$MEPSTATEFIPS, 2, pad = "0")
data$MEPCOUNTY3 <- stringr::str_pad(data$MEPCOUNTY3, 3, pad = "0")

data$MASTSTATEFIPS <- stringr::str_pad(data$MASTSTATEFIPS, 2, pad = "0")
data$MASTCOUNTY3 <- stringr::str_pad(data$MASTCOUNTY3, 3, pad = "0")

data$MEPCOUNTY5 <- stringr::str_pad(data$MEPCOUNTY5, 5, pad = "0")
data$MASTCOUNTY5 <- stringr::str_pad(data$MASTCOUNTY5, 5, pad = "0")
data$MEPCOUNTY5.CB <- dplyr::coalesce(data$MEPCOUNTY5, data$MASTCOUNTY5)
data$MEPCOUNTY5.CB <- as.character(data$MEPCOUNTY5.CB)
data$MEPCOUNTY5.CB[data$MEPCOUNTY5.CB == ""] <- NA
data$MEPCOUNTY5.CB <- stringr::str_pad(data$MEPCOUNTY5.CB, 5, pad = "0")
data %>% dplyr::select(PID_PDE, MEPCOUNTY5, MASTCOUNTY5, MEPCOUNTY5.CB)
(sum(is.na(data$MEPCOUNTY5.CB))/length(data$PID_PDE))*100 # 2.21%


#END
#### Create new variables -----------------------------------------------------------

# load in data
data <- read.csv("\\\\facaa7pde01p\\PDE\\Projects\\ARI\\ARI-SDAL\\Army20Yr_linked_data.csv", header = TRUE, 
                 stringsAsFactors = FALSE, na.strings = c("NA", "NaN", "", " "), fill = TRUE)

### Coalesce variables (.CB)

## Birth date [missing = 0.0064]
data$DATE_BIRTH.CB <- dplyr::coalesce(data$DATE_BIRTH_PDE, data$DATE_BIRTH.x, data$DATE_BIRTH.y)
data$DATE_BIRTH.CB <- lubridate::as_date(data$DATE_BIRTH.CB)

## Faith Group [missing = 0.024]
# Place NAs for blanks
data$FAITH_GRP_CD <- as.character(data$FAITH_GRP_CD)
data$FAITH_GRP_CD[data$FAITH_GRP_CD == ""] <- NA
data$PN_FAITH_GRP_CD <- as.character(data$PN_FAITH_GRP_CD)
data$PN_FAITH_GRP_CD[data$PN_FAITH_GRP_CD == ""] <- NA
# Recode faith variables (No preference = 1, atheist = 2, agnostic = 3, christian = 4, jewish = 5, muslim = 6, hindu = 7, buddist = 8, sikh = 9, other = 10)
sort(unique(data$FAITH_GRP_CD))
data <- data %>% dplyr::mutate(FAITH_GRP_CD.R = dplyr::recode(data$FAITH_GRP_CD, "AC" = 4, "AJ" = 4, "AS" = 4, "AV" = 4, "BA" = 4, "BB" = 4, "BC" = 4, "BF" = 4, "BG" = 4, "BN" = 4, "BP" = 4, "BR" = 4, 
                                                              "BT" = 4, "BU" = 4, "CC" = 4, "CR" = 4, "DL" = 4, "DR" = 4, "EC" = 4, "EE" = 4, "ER" = 4, "FA" = 4, "FB" = 4, "FC" = 4, 
                                                              "FF" = 4, "FG" = 4, "GC" = 4, "GE" = 4, "GG" = 4, "GT" = 4, "GX" = 4, "HA" = 4, "HC" = 4, "HN" = 4, "HS" = 4, "II" = 6,
                                                              "JJ" = 5, "KB" = 8, "KF" = 10, "KH" = 7, "LE" = 4, "LL" = 4, "LM" = 4, "MC" = 4, "ME" = 4, "MM" = 4, "MN" = 4, "MR" = 4,
                                                              "MU" = 4, "MW" = 4, "MZ" = 4, "NC" = 4, "NO" = 1, "OE" = 4, "OO" = 4, "PA" = 4, "PC" = 4, "PD" = 4, "PF" = 4, "PG" = 4,
                                                              "PH" = 4, "PJ" = 4, "PP" = 4, "PS" = 4, "PT" = 4, "PU" = 4, "QB" = 4, "QF" = 4, "QQ" = 4, "QS" = 4, "RB" = 4, "RC" = 4,
                                                              "RD" = 4, "RF" = 4, "RG" = 4, "RI" = 4, "RP" = 4, "RR" = 4, "RU" = 4, "SC" = 4, "TN" = 4, "TO" = 4, "UU" = 4, "VA" = 4,
                                                              "VB" = 4, "VE" = 4, "VF" = 4, "VM" = 4, "VP" = 4, "VV" = 4, "XC" = 4, "XN" = 4, "XX" = 4, "YW" = 10, "YY" = 10, "ZA" = 2, "ZB"  = 3))

sort(unique(data$PN_FAITH_GRP_CD))
data <- data %>% dplyr::mutate(PN_FAITH_GRP_CD.R = dplyr::recode(data$PN_FAITH_GRP_CD, "00" = 1, "01" = 1, "02" = 4, "04" = 4, "05" = 4, "06" = 4, "07" = 4, "08" = 4, "09" = 4, "10" = 4, "12" = 4, 
                                                                 "13" = 4, "14" = 8, "16" = 4, "18" = 4, "19" = 4, "20" = 4, "24" = 4, "26" = 4, "32" = 4, "34" = 4, "36" = 5, "38" = 4, "40" = 4, 
                                                                 "41" = 4, "44" = 4, "45" = 4, "46" = 4, "47" = 4, "48" = 6, "49" = 7, "50" = 4, "53" = 4, "55" = 4, "56" = 4, "57" = 4, "58" = 4,
                                                                 "60" = 4, "62" = 4, "64" = 4, "66" = 4, "68" = 4, "70" = 4, "72" = 4, "74" = 10, "75" = 2, "99" = 1, "A1" = 4, "A3" = 4, "A4" = 4,
                                                                 "A5" = 4, "A6" = 4, "A7" = 4, "AA" = 4, "AB" = 4, "AC" = 4, "AD" = 4, "AE" = 4, "AF" = 4, "AG" = 4, "AH" = 4, "AJ" = 4, "AK" = 4, "AL" = 4,
                                                                 "AM" = 4, "AN" = 10, "AO" = 4, "AQ" = 4, "AR" = 4, "AS" = 4, "AT" = 4, "AV" = 4, "AX" = 4, "B1" = 4, "B4" = 4, "BA" = 4, "BB" = 4, "BC" = 4,
                                                                 "BD" = 4, "BE" = 4, "BF" = 4, "BG" = 4, "BH" = 4, "BI" = 4, "BO" = 4, "BU" = 4, "BV" = 10, "C2" = 4, "C4" = 4, "C7" = 4, "C9" = 4, "CA" = 4, 
                                                                 "CC" = 4, "CD" = 4, "CE" = 4, "CF" = 4, "CG" = 4, "CH" = 4, "CI" = 4, "CJ" = 4, "CL" = 4, "CO" = 4, "CR" = 4, "CY" = 4, "D2" = 4, "D6" = 4, 
                                                                 "DA" = 4, "DB" = 4, "DC" = 4, "DD" = 4, "DE" = 4, "DF" = 4, "DG" = 4, "DH" = 4, "DJ" = 4, "DL" = 4, "DM" = 4, "DN" = 4, "DO" = 4, "DP" = 4, 
                                                                 "DQ" = 4, "DR" = 4, "DS" = 4, "DT" = 4, "DU" = 4, "DV" = 4, "DW" = 4, "DX" = 4, "DY" = 4, "DZ" = 4, "E3" = 9, "EA" = 4, "EC" = 4, "ED" = 4, 
                                                                 "EF" = 4, "EH" = 4, "EJ" = 4, "EK" = 4, "EL" = 4, "EM" = 4, "EN" = 4, "EO" = 4, "EP" = 4, "ER" = 4, "ES" = 4, "ET" = 4, "EU" = 4, "F5" = 4, 
                                                                 "F6" = 4, "F8" = 4, "F9" = 4, "FA" = 5, "FB" = 5, "FC" = 5, "FE" = 4, "FG" = 4, "FI" = 4, "FN" = 4, "FY" = 10, "FZ" = 4, "G3" = 10, "G5" = 10,
                                                                 "GA" = 4, "GB" = 4, "GC" = 4, "GD" = 4, "GE" = 4, "GG" = 4, "GX" = 4, "HA" = 4, "HC" = 4, "HN" = 4, "HS" = 4, "II" = 6, "JA" = 4, "JB" = 4, 
                                                                 "JC" = 4, "JD" = 4, "JE" = 4, "JF" = 4, "JG" = 4, "JH" = 4, "JJ" = 4, "JK" = 4, "JL" = 4, "JM" = 4, "JN" = 4, "JO" = 4, "JP" = 4, "JQ" = 4, 
                                                                 "JR" = 4, "JS" = 4, "JT" = 4, "JU" = 4, "JV" = 4, "JW" = 4, "JX" = 4, "JY" = 4, "KB" = 8, "KH" = 7, "LA" = 4, "LB" = 4, "LC" = 4, "LD" = 4, 
                                                                 "LE" = 4, "LF" = 4, "LG" = 4, "LH" = 4, "LJ" = 4, "LL" = 4, "LM" = 4, "MC" = 4, "ME" = 4, "MJ" = 4, "MM" = 4, "MN" = 4, "MR" = 4, "MU" = 4,
                                                                 "MW" = 4, "MZ" = 4, "NB" = 4, "NC" = 4, "ND" = 4, "NE" = 4, "NO" = 1, "OE" = 4, "OO" = 4, "PA" = 4, "PC" = 4, "PD" = 4, "PG" = 4, "PH" = 4, 
                                                                 "PJ" = 4, "PP" = 4, "PS" = 4, "PT" = 4, "PU" = 4, "QB" = 4, "QF" = 4, "QS" = 4, "RC" = 4, "RD" = 4, "RG" = 4, "RI" = 4, "RP" = 4, "RR" = 4, 
                                                                 "RU" = 4, "SC" = 4, "TN" = 4, "TO" = 4, "UU" = 4, "VA" = 4, "VF" = 4, "VM" = 4, "VP" = 4, "VV" = 4, "XC" = 4, "XN" = 4, "YW" = 10, "YY" = 10, 
                                                                 "ZA" = 2, "ZB"  = 3, "ZW" = 1, "ZX" = 1, "ZY" = 1))                                  
# Coalesce faith vars             
data$FAITH_GRP.CB <- dplyr::coalesce(data$FAITH_GRP_CD.R, data$PN_FAITH_GRP_CD.R)
data$FAITH_GRP.CB <- factor(data$FAITH_GRP.CB)

## Marital Status [missing = 0.000007]
data$MRTL_STAT.CB <- dplyr::coalesce(data$MRTL_STAT_CD, data$PN_MRTL_STAT_CD)
data$MRTL_STAT.CB <- as.character(data$MRTL_STAT.CB)
data$MRTL_STAT.CB[data$MRTL_STAT.CB == ""] <- NA
data$MRTL_STAT.CB <- factor(data$MRTL_STAT.CB)

## Home State [missing = 0.0406]
data$HOR_STATE.CB <- dplyr::coalesce(data$HOR_US_ST_CD, data$STATE, data$PN_MA_US_ST_CD)
data$HOR_STATE.CB <- as.character(data$HOR_STATE.CB)
data$HOR_STATE.CB[data$HOR_STATE.CB == ""] <- NA
data$HOR_STATE.CB <- factor(data$HOR_STATE.CB)

## Home Zip [missing = 0.062]
data$HOR_ZIPCODE.CB <- dplyr::coalesce(data$ZIP_CODE_PDE_PN_MA, data$ZIP_CODE_PDE)
data$HOR_ZIPCODE.CB <- as.character(data$HOR_ZIPCODE.CB)
data$HOR_ZIPCODE.CB[data$HOR_ZIPCODE.CB == ""] <- NA

## AFQT [missing = 0.0011]
data$AFQT_PCTL.CB <- dplyr::coalesce(data$AFQT_PCTL_SCR_QY.y, data$AFQT_PCTL_SCR_QY.x, data$AFQT)

#REDO
data$AFQT_PCTL_SCR_QY.y[data$AFQT_PCTL_SCR_QY.y == 0] <- NA # changed to zero due to large amounts coded as such in error perhaps
data$AFQT_PCTL_SCR_QY.x[data$AFQT_PCTL_SCR_QY.x == 0] <- NA # changed to zero due to large amounts coded as such in error perhaps
data$AFQT[data$AFQT == 0] <- NA # changed to zero due to large amounts coded as such in error perhaps
data$AFQT_PCTL.CB <- dplyr::coalesce(data$AFQT_PCTL_SCR_QY.y, data$AFQT_PCTL_SCR_QY.x, data$AFQT)
data$AFQT_PCTL.CB[data$AFQT_PCTL.CB == 0] <- NA # changed to zero due to large amounts coded as such in error perhaps
#a <- data %>% dplyr::select(AFQT_PCTL_SCR_QY.y, AFQT_PCTL_SCR_QY.x, AFQT, AFQT_PCTL.CB)

## Rank groups for enlisted (1), warrant officer (2), officer (3) 
data <- data %>% dplyr::mutate(RANK_PDE_GRP = dplyr::recode(data$RANK_PDE, "PV1" = "Enlisted", "PV2" = "Enlisted", "PFC" = "Enlisted", "CPL" = "Enlisted", "SPC" = "Enlisted", "SGT" = "Enlisted", "SSG" = "Enlisted", "SFC" = "Enlisted",
                                                            "EEE" = "Enlisted", "WO1" = "Warrant Officer", "CW2" = "Warrant Officer", "CW3" = "Warrant Officer", "WWW" = "Warrant Officer", "2LT" = "Officer", "1LT" = "Officer", "CPT" = "Officer", "MAJ" = "Officer", "OOO" = "Officer"))
## Rank groups (last)
data <- data %>% dplyr::mutate(RANK_PDE_GRP_last = dplyr::recode(data$RANK_PDE_last, "PV1" = "Enlisted", "PV2" = "Enlisted", "PFC" = "Enlisted", "CPL" = "Enlisted", "SPC" = "Enlisted", "SGT" = "Enlisted", "SSG" = "Enlisted", "SFC" = "Enlisted",
                                                                 "EEE" = "Enlisted", "WO1" = "Warrant Officer", "CW2" = "Warrant Officer", "CW3" = "Warrant Officer", "WWW" = "Warrant Officer", "2LT" = "Officer", "1LT" = "Officer", "CPT" = "Officer", "MAJ" = "Officer", "OOO" = "Officer"))
## MOS [missing = 0.0008] 
data$PRI_SVC_OCC_CD <- as.character(data$PRI_SVC_OCC_CD)
data$PRI_SVC_OCC_CD[data$PRI_SVC_OCC_CD == ""] <- NA
data$PRI_SVC_OCC_CD <- substr(data$PRI_SVC_OCC_CD, 1, 3) # only take first three digits of mos

data$MOS <- as.character(data$MOS)
data$MOS[data$MOS == ""] <- NA
data$MOS <- substr(data$MOS, 1, 3) # only take first three digits of mos

data$ACC_PRI_SVC_OCC_CD <- as.character(data$ACC_PRI_SVC_OCC_CD)
data$ACC_PRI_SVC_OCC_CD[data$ACC_PRI_SVC_OCC_CD == ""] <- NA
data$ACC_PRI_SVC_OCC_CD <- substr(data$ACC_PRI_SVC_OCC_CD, 1, 3) # only take first three digits of mos

# Coalesce MOS
data$MOS.CB <- dplyr::coalesce(data$PRI_SVC_OCC_CD, data$MOS, data$ACC_PRI_SVC_OCC_CD)
data$MOS.CB <- as.character(data$MOS.CB)
data$MOS.CB[data$MOS.CB == ""] <- NA

## MOS_NAME
data$MOS.CB <- as.character(data$MOS.CB)
data$RANK_PDE_GRP <- as.character(data$RANK_PDE_GRP)
data <- data %>% dplyr::mutate(MOS_NAME = case_when(data$RANK_PDE_GRP == "Enlisted" ~ dplyr::recode(data$MOS.CB, "00B" = "(00B) Diver", "00D" = "(00D) Special Duty Assignment", "00F" = "(00F) MOS Immaterial NGB", 
                                                                                                    "00U" = "(00U) Equal Opportunity Specialist", "00Z" = "(00Z) Command Sergeant Major", "02A" = "(02A) Army Bandperson", "02B" = "(02B) Cornet or Trumpet Player", 
                                                                                                    "02C" = "(02C) Euphonium Player", "02D" = "(02D) French Horn Player", "02E" = "(02E) Trombone Player", "02F" = "(02F) Tuba Player", "02G" = "(02G) Flute or Piccolo Player", 
                                                                                                    "02H" = "(02H) Oboe Player", "02J" = "(02J) Clarinet Player", "02K" = "(02K) Bassoon Player", "02L" = "(02L) Saxophone Player", "02M" = "(02M) Percussion Player", 
                                                                                                    "02N" = "(02N) Keyboard Player", "02T" = "(02T) Guitar Player", "02U" = "(02U) Electric Bass Player", "02Z" = "(02Z) Bands Senior Sergeant", "09B" = "(09B) Basic Trainee", 
                                                                                                    "09C" = "(09C) Trainee Language", "09D" = "(09D) College Trainee", "09L" = "(09L) Translator Aide", "09R" = "(09R) Simultaneous Membership Program Participant (RC)", 
                                                                                                    "09S" = "(09S) Commissioned Officer Candidate", "09W" = "(09W) Warrant Officer Candidate", "11B" = "(11B) Light Weapons Infantryman", "11C" = "(11C) Infantry Indirect Fire Crewman", 
                                                                                                    "11H" = "(11H) Heavy Antiarmor Weapons Infantryman", "11M" = "(11M) Fighting Vehicle Infantryman", "11X" = "(11X) Infantryman", "11Z" = "(11Z) Infantry Senior Sergeant", 
                                                                                                    "12B" = "(12B) Combat Engineer", "12C" = "(12C) Bridge Crewmember", "12Z" = "(12Z) Combat Engineering Senior Sergeant", "13B" = "(13B) Cannon Crewmember", 
                                                                                                    "13C" = "(13C) Tactical Automated Fire Control Systems Specialist", "13D" = "(13D) Field Artillery Automated Tactical Data System Specialist", "13E" = "(13E) Cannon Fire Direction Specialist", 
                                                                                                    "13F" = "(13F) Fire Support Specialist", "13M" = "(13M) Multiple Launch Rocket System (MLRS) Crewmember", "13P" = "(13P) Multiple Launch Rocket System (MLRS) Operational Fire Direction", 
                                                                                                    "13R" = "(13R) Field Artillery Firefinder Radar Operator", "13S" = "(13S) Field Artillery Surveyor", "13W" = "(13W) Field Artillery Meteorological Crewmember", "13X" = "(13X) Field Artillery Crewmember", 
                                                                                                    "13Z" = "(13Z) Field Artillery Senior Sergeant", "14D" = "(14D) HAWK Missile System Crewmember", "14E" = "(14E) PATRIOT Fire Control Enhanced Operator/Maintainer", "14J" = "(14J) Air Defense C4I Tactical Operations Center Enhanced Operator/Mai", 
                                                                                                    "14M" = "(14M) Man Portable Air Defense System Crewmember (RC)", "14R" = "(14R) BRADLEY Linebacker Crewmember", "14S" = "(14S) AVENGER Crewmember", "14T" = "(14T) PATRIOT Launching Station Enhanced Operator/Maintainer", "14Z" = "(14Z) Air Defense Artillery Senior Sergeant", 
                                                                                                    "15B" = "(15B) Aircraft Powerplant Repairer", "15D" = "(15D) Aircraft Powertrain Repairer", "15F" = "(15F) Aircraft Electrician", "15G" = "(15G) Aircraft Structural Repairer", "15H" = "(15H) Aircraft Pneudraulics Repairer", 
                                                                                                    "15J" = "(15J) OH 58D Armament/Electrical/Avionics Systems Repairer", "15K" = "(15K) Aircraft Components Repair Supervisor", "15M" = "(15M) UH 1 Helicopter Repairer (RC)", "15N" = "(15N) Avionic Mechanic", "15P" = "(15P) Aviation Operations Specialist", 
                                                                                                    "15Q" = "(15Q) Air Traffic Control Operator", "15R" = "(15R) AH 64 Attack Helicopter Repairer", "15S" = "(15S) OH 58D Helicopter Repairer", "15T" = "(15T) UH 60 Helicopter Repairer", "15U" = "(15U) CH 47 Helicopter Repairer", 
                                                                                                    "15V" = "(15V) Observation/Scout Helicopter Repairer (RC)", "15X" = "(15X) AH 64A Armament/Electrical/Avionics Systems Repairer", "15Y" = "(15Y) AH 64D Armament/Electrical/Avionics Systems Repairer", 
                                                                                                    "15Z" = "(15Z) Aircraft Maintenance Senior Sergeant", "16F" = "(16F) Light Air Defense Artillery Crewmember (Reserve Forces)", "18B" = "(18B) Special Forces Weapons Sergeant", "18C" = "(18C) Special Forces Engineer Sergeant", 
                                                                                                    "18D" = "(18D) Special Forces Medical Sergeant", "18E" = "(18E) Special Forces Communications Sergeant", "18F" = "(18F) Special Forces Assistant Operations and Intelligence Sergeant", 
                                                                                                    "18X" = "(18X) Special Forces Sergeant", "18Z" = "(18Z) Special Forces Senior Sergeant", "19D" = "(19D) Cavalry Scout", "19K" = "(19K) M1 Armor Crewman", "19Z" = "(19Z) Armor Senior Sergeant", 
                                                                                                    "21B" = "(21B) Combat Engineer", "21C" = "(21C) Bridge Crewmember", "21D" = "(21D) Diver", "21E" = "(21E) Heavy Construction Equipment Operator", "21F" = "(21F) Crane Operator", 
                                                                                                    "21G" = "(21G) Quarrying Specialist (RC)", "21H" = "(21H) Construction Engineering Supervisor", "21J" = "(21J) General Construction Equipment Operator", "21K" = "(21K) Plumber", 
                                                                                                    "21L" = "(21L) Lithographer", "21M" = "(21M) Fire Fighter", "21N" = "(21N) Construction Equipment Supervisor", "21P" = "(21P) Prime Power Production Specialist", 
                                                                                                    "21Q" = "(21Q) Transmission and Distribution Specialist (RC)", "21R" = "(21R) Interior Electrician", "21S" = "(21S) Topographic Surveyor", "21T" = "(21T) Technical Engineer", 
                                                                                                    "21U" = "(21U) Topographic Analyst", "21V" = "(21V) Concrete and Asphalt Equipment Operator", "21W" = "(21W) Carpentry and Masonry Specialist", "21X" = "(21X) General Engineering Supervisor", 
                                                                                                    "21Y" = "(21Y) Topographic Engineering Supervisor", "21Z" = "(21Z) Combat Engineering Senior Sergeant", "24N" = "(24N) CHAPARRAL System Mechanic", "25B" = "(25B) Information Systems Operator Analyst", 
                                                                                                    "25C" = "(25C) Radio Operator Maintainer", "25D" = "(25D) Telecommunications Operator Maintainer", "25F" = "(25F) Network Switching Systems Operator Maintainer", "25L" = "(25L) Cable Systems Installer Maintainer", 
                                                                                                    "25M" = "(25M) Multimedia Illustrator", "25P" = "(25P) Microwave Systems Operator Maintainer", "25Q" = "(25Q) Multichannel Transmission Systems Operator Maintainer", "25R" = "(25R) Visual Information Equipment Operator Maintainer", 
                                                                                                    "25S" = "(25S) Satellite Communications Systems Operator Maintainer", "25T" = "(25T) Satellite/Microwave Systems Chief", "25U" = "(25U) Signal Support Systems Specialist", "25V" = "(25V) Combat Documentation/Production Specialist", 
                                                                                                    "25W" = "(25W) Telecommunications Operations Chief", "25X" = "(25X) Senior Signal Sergeant", "25Y" = "(25Y) Information Systems Chief", "25Z" = "(25Z) Visual Information Operations Chief", "27D" = "(27D) Paralegal Specialist", 
                                                                                                    "27E" = "(27E) Land Combat Electronic Missile System Repairer", "27M" = "(27M) Multiple Launch Rocket System (MLRS) Repairer", "27T" = "(27T) AVENGER System Repairer", "27X" = "(27X) PATRIOT System Repairer", "27Z" = "(27Z) Missile Systems Maintenance Chief", 
                                                                                                    "31B" = "(31B) Military Police", "31C" = "(31C) Radio Operator Maintainer", "31D" = "(31D) CID Special Agent", "31E" = "(31E) Internment / Resettlement Specialist", "31F" = "(31F) Network Switching Systems Operator Maintainer", "31L" = "(31L) Cable Systems Installer Maintainer", 
                                                                                                    "31M" = "(31M) Multichannel Transmission Systems Operator", "31N" = "(31N) Communications Systems/Circuit Controller", "31P" = "(31P) Microwave Systems Operator Maintainer", "31R" = "(31R) Multichannel Transmission Systems Operator Maintainer", 
                                                                                                    "31S" = "(31S) Satellite Communications Systems Operator Maintainer", "31T" = "(31T) Satellite/Microwave Systems Chief", "31U" = "(31U) Signal Support Systems Specialist", "31W" = "(31W) Telecommunications Operations Chief", "31Z" = "(31Z) Senior Signal Sergeant", 
                                                                                                    "33T" = "(33T) Electronic Warfare/Intercept Tactical Systems Repairer", "33W" = "(33W) Military Intelligence Systems Maintainer/Integrator", "33Z" = "(33Z) EW/Intercept Systems Maintenance Supervisor", "35A" = "(35A) Land Combat Electronics Missile System Repairer", 
                                                                                                    "35B" = "(35B) Land Combat Support Systems (LCSS) Test Specialist", "35D" = "(35D) Air Traffic Control Equipment Repairer", "35E" = "(35E) Special Electrical Devices Repairer", "35F" = "(35F) Nuclear Weapons Electronics Specialist", "35H" = "(35H) TMDE Maintenance Support Specialist", 
                                                                                                    "35J" = "(35J) Computer/Automation Systems Repairer", "35K" = "(35K) Avionic Mechanic", "35L" = "(35L) Avionic Communications Equipment Repairer", "35M" = "(35M) Radar Repairer", "35N" = "(35N) Wire Systems Equipment Repairer", "35P" = "(35P) Multiple Launch Rocket System (MLRS) Repairer", 
                                                                                                    "35Q" = "(35Q) Avionic Flight Systems Repairer", "35R" = "(35R) Avionic Systems Repairer", "35S" = "(35S) Electronic Biomedical Equipment Repairer", "35T" = "(35T) X Ray Biomedical Equipment Repairer", "35V" = "(35V) Electronic and Missile Systems Maintenance Chief", 
                                                                                                    "35W" = "(35W) Electronic Maintenance Chief", "35Y" = "(35Y) Integrated Family of Test Equipment Operator/Maintainer", "35Z" = "(35Z) Senior Electronics Maintenance Chief", "37F" = "(37F) Psychological Operations Specialist", "38A" = "(38A) Civil Affairs Specialist (RC)", 
                                                                                                    "38B" = "(38B) Civil Affairs Specialist", "39B" = "(39B) Automatic Test Equipment Operator/Maintainer", "42A" = "(42A) Human Resources Specialist", "42E" = "(42E) Optical Laboratory Specialist", "42F" = "(42F) Human Resources Information Systems Management Specialist", 
                                                                                                    "42L" = "(42L) Administrative Specialist", "42R" = "(42R) Army Bandperson", "43M" = "(43M) Fabric Repair Specialist", "44B" = "(44B) Metal Worker", "44C" = "(44C) Welder", "44E" = "(44E) Machinist", "45B" = "(45B) Small Arms/Artillery Repairer", 
                                                                                                    "45D" = "(45D) Self Propelled Field Artillery Turret Mechanic", "45E" = "(45E) M1 ABRAMS Tank Turret Mechanic", "45G" = "(45G) Fire Control Repairer", "45K" = "(45K) Armament Repairer", "45N" = "(45N) M60A1/A3 Tank Turret Mechanic (RC)", "45T" = "(45T) BRADLEY Fighting Vehicle System Turret Mechanic", 
                                                                                                    "46Q" = "(46Q) Public Affairs Specialist", "46R" = "(46R) Public Affairs Broadcast Specialist", "46Z" = "(46Z) Chief Public Affairs NCO", "51B" = "(51B) Carpentry and Masonry Specialist", "51H" = "(51H) Construction Engineering Supervisor", "51K" = "(51K) Plumber", "51M" = "(51M) Fire Fighter", 
                                                                                                    "51R" = "(51R) Interior Electrician", "51T" = "(51T) Technical Engineering Specialist", "51Z" = "(51Z) General Engineering Supervisor", "52C" = "(52C) Utilities Equipment Repairer", "52D" = "(52D) Power Generation Equipment Repairer", "52E" = "(52E) Prime Power Production Specialist", 
                                                                                                    "52G" = "(52G) Transmission and Distribution Specialist (RC)", "52X" = "(52X) Special Purpose Equipment Repairer", "54B" = "(54B) Chemical Operations Specialist", "55B" = "(55B) Ammunition Specialist", 
                                                                                                    "55D" = "(55D) Explosive Ordnance Disposal Specialist", "56M" = "(56M) Chaplain Assistant", "57E" = "(57E) Laundry and Bath Specialist", "62B" = "(62B) Construction Equipment Repairer", 
                                                                                                    "62E" = "(62E) Heavy Construction Equipment Operator", "62F" = "(62F) Crane Operator", "62G" = "(62G) Quarrying Specialist (RC)", "62H" = "(62H) Concrete and Asphalt Equipment Operator", 
                                                                                                    "62J" = "(62J) General Construction Equipment Operator", "62N" = "(62N) Construction Equipment Supervisor", "63A" = "(63A) M1 ABRAMS Tank System Maintainer", "63B" = "(63B) Light Wheel Vehicle Mechanic", 
                                                                                                    "63D" = "(63D) Artillery Mechanic", "63E" = "(63E) M1 ABRAMS Tank System Mechanic", "63G" = "(63G) Fuel and Electrical System Repairer", "63H" = "(63H) Track Vehicle Repairer", 
                                                                                                    "63J" = "(63J) Quartermaster and Chemical Equipment Repairer", "63M" = "(63M) BRADLEY Fighting Vehicle System Maintainer", "63N" = "(63N) M60A1/A3 Tank System Mechanic", 
                                                                                                    "63S" = "(63S) Heavy Wheel Vehicle Mechanic", "63T" = "(63T) BRADLEY Fighting Vehicle System Mechanic", "63W" = "(63W) Wheel Vehicle Repairer", "63X" = "(63X) Vehicle Maintenance Supervisor", 
                                                                                                    "63Y" = "(63Y) Track Vehicle Mechanic", "63Z" = "(63Z) Mechanical Maintenance Supervisor", "67G" = "(67G) Utility Airplane Repairer (RC)", "67H" = "(67H) Observation Airplane Repairer", 
                                                                                                    "67N" = "(67N) UH 1 Helicopter Repairer", "67R" = "(67R) AH 64 Attack Helicopter Repairer", "67S" = "(67S) OH 58D Scout Helicopter Repairer", "67T" = "(67T) UH 60 Helicopter Repairer", 
                                                                                                    "67U" = "(67U) CH 47 Helicopter Repairer", "67V" = "(67V) Observation/Scout Helicopter Repairer", "67Y" = "(67Y) AH 1 Attack Helicopter Repairer (RC)", 
                                                                                                    "67Z" = "(67Z) Aircraft Maintenance Senior Sergeant", "68A" = "(68A) Aircraft Repairer", "68B" = "(68B) Aircraft Powerplant Repairer", "68D" = "(68D) Aircraft Powertrain Repairer", 
                                                                                                    "68E" = "(68E) Aircraft Rotor and Propeller Repairman", "68F" = "(68F) Aircraft Electrician", "68G" = "(68G) Aircraft Structural Repairer", "68H" = "(68H) Aircraft Pneudraulics Repairer", 
                                                                                                    "68J" = "(68J) Aircraft Armament/Missile Systems Repairer (RC)", "68K" = "(68K) Aircraft Components Repair Supervisor", "68N" = "(68N) Avionic Mechanic", 
                                                                                                    "68P" = "(68P) Avionic Maintenance Supervisor", "68Q" = "(68Q) Avionic Flight Systems Repairer", "68S" = "(68S) OH 58D Armament/Electrical/Avionics Systems Repairer", 
                                                                                                    "68W" = "(68W) Avionic Armament/Electrical/Avionics Systems Repairer", "68X" = "(68X) AH 64A Armament/Electrical Systems Repairer", "68Y" = "(68Y) AH 64D Armament/Electrical/Avionics Systems Repairer", 
                                                                                                    "68Z" = "(68Z) Avionic Armament/Electrical/Avionics Systems Repairer", "71D" = "(71D) Legal Specialist", "71G" = "(71G) Patient Administration Specialist", "71L" = "(71L) Administrative Specialist", 
                                                                                                    "71M" = "(71M) Chaplain Assistant", "73C" = "(73C) Finance Specialist", "73D" = "(73D) Accounting Specialist", "73Z" = "(73Z) Finance Senior Sergeant", "74B" = "(74B) Information Systems Operator Analyst", 
                                                                                                    "74C" = "(74C) Telecommunications Operator Maintainer", "74D" = "(74D) Information System Operator", "74G" = "(74G) Telecommunications Computer Operator Maintainer", "74Z" = "(74Z) Information Systems Chief", 
                                                                                                    "75B" = "(75B) Personnel Administration Specialist", "75F" = "(75F) Personnel Information Systems Management Specialist", "75H" = "(75H) Personnel Services Specialist", "75Z" = "(75Z) Personnel Sergeant", 
                                                                                                    "76J" = "(76J) Medical Supply Specialist", "77F" = "(77F) Petroleum Supply Specialist", "77L" = "(77L) Petroleum Laboratory Specialist", "77W" = "(77W) Water Treatment Specialist", "79R" = "(79R) Recruiter", 
                                                                                                    "79S" = "(79S) Career Counselor", "79T" = "(79T) Recruiting and Retention NCO (Army National Guard of the United", "79V" = "(79V) Retention and Transition NCO USAR", "81L" = "(81L) Lithographer", 
                                                                                                    "81T" = "(81T) Topographic Analyst", "81Z" = "(81Z) Topographic Engineering Supervisor", "82C" = "(82C) Field Artillery Surveyor", "82D" = "(82D) Topographic Surveyor", 
                                                                                                    "88H" = "(88H) Cargo Specialist", "88K" = "(88K) Watercraft Operator", "88L" = "(88L) Watercraft Engineer", "88M" = "(88M) Motor Transport Operator", 
                                                                                                    "88N" = "(88N) Transportation Management Coordinator", "88P" = "(88P) Railway Equipment Repairer (RC)", "88T" = "(88T) Railway Section Repairer (RC)", 
                                                                                                    "88U" = "(88U) Railway Operations Crewmember (RC)", "88X" = "(88X) Railway Senior Sergeant (RC)", "88Z" = "(88Z) Transportation Senior Sergeant", "89B" = "(89B) Ammunition Specialist", 
                                                                                                    "89D" = "(89D) Explosive Ordnance Disposal Specialist", "91A" = "(91A) Medical Equipment Repairer", "91B" = "(91B) Medical Specialist", "91C" = "(91C) Practical Nurse", 
                                                                                                    "91D" = "(91D) Operating Room Specialist", "91E" = "(91E) Dental Specialist", "91G" = "(91G) Behavioral Science Specialist", "91H" = "(91H) Optical Laboratory Specialist", 
                                                                                                    "91J" = "(91J) Medical Logistics Specialist", "91K" = "(91K) Medical Laboratory Specialist", "91M" = "(91M) Nutrition Care Specialist", "91P" = "(91P) Radiology Specialist", 
                                                                                                    "91Q" = "(91Q) Pharmacy Specialist", "91R" = "(91R) Veterinary Food Inspection Specialist", "91S" = "(91S) Preventive Medicine Specialist", "91T" = "(91T) Animal Care Specialist", 
                                                                                                    "91V" = "(91V) Respiratory Specialist", "91W" = "(91W) Health Care Specialist", "91X" = "(91X) Mental Health Specialist", "91Z" = "(91Z) Medical Senior Sergeant", 
                                                                                                    "92A" = "(92A) Automated Logistical Specialist", "92F" = "(92F) Petroleum Supply Specialist", "92G" = "(92G) Food Service Operations", "92L" = "(92L) Petroleum Laboratory Specialist", 
                                                                                                    "92M" = "(92M) Mortuary Affairs Specialist", "92R" = "(92R) Parachute Rigger", "92S" = "(92S) Shower/Laundry and Clothing Repair Specialist", "92W" = "(92W) Water Treatment Specialist", 
                                                                                                    "92Y" = "(92Y) Unit Supply Specialist", "92Z" = "(92Z) Senior Non Commissioned Logistician", "93B" = "(93B) Aeroscout Observer", "93C" = "(93C) Air Traffic Control Operator", 
                                                                                                    "93F" = "(93F) Field Artillery Meteorological Crewmember", "93P" = "(93P) Aviation Operations Specialist", "94A" = "(94A) Land Combat Electronic Missile System Repairer", 
                                                                                                    "94D" = "(94D) Air Traffic Control Equipment Repairer", "94E" = "(94E) Radio and Communications Security (COMSEC) Repairer", "94F" = "(94F) Special Electronic Devices Repairer", 
                                                                                                    "94H" = "(94H) TMDE Maintenance Support Specialist", "94K" = "(94K) APACHE Attack Helicopter Systems Repairer", "94L" = "(94L) Avionic Communications Equipment Repairer", 
                                                                                                    "94M" = "(94M) Radar Repairer", "94P" = "(94P) Multiple Launch Rocket System (MLRS) Repairer", "94R" = "(94R) Avionic Systems Repairer", "94S" = "(94S) PATRIOT System Repairer", 
                                                                                                    "94T" = "(94T) AVENGER System Repairer", "94W" = "(94W) Electronic Maintenance Chief", "94Y" = "(94Y) Integrated Family of Test Equipment Operator/Maintainer", 
                                                                                                    "94Z" = "(94Z) Senior Electronics Maintenance Chief", "95B" = "(95B) Military Police", "95C" = "(95C) Internment/Resettlement Specialist", "95D" = "(95D) CID Special Agent", 
                                                                                                    "96B" = "(96B) Intelligence Analyst", "96D" = "(96D) Imagery Analyst", "96H" = "(96H) Common Ground Station Operator", "96R" = "(96R) Ground Surveillance Systems Operator", 
                                                                                                    "96U" = "(96U) Tactical Unmanned Aerial Vehicle Operator", "96Z" = "(96Z) Intelligence Senior Sergeant", "97B" = "(97B) Counterintelligence Agent", "97E" = "(97E) Human Intelligence Collector", 
                                                                                                    "97L" = "(97L) Translator/Interpreter (RC)", "97Z" = "(97Z) Counterintelligence/Human Intelligence Senior Sergeant", "98C" = "(98C) Signals Intelligence Analyst", 
                                                                                                    "98G" = "(98G) Cryptologic Communications Interceptor/Locator", "98H" = "(98H) Communications Interceptor/Locator", "98J" = "(98J) Electronic Intelligence Interceptor/Analyst", 
                                                                                                    "98K" = "(98K) Signals Collection/Identification Analyst", "98P" = "(98P) Multi Sensor Operator", "98X" = "(98X) Signal Intelligence Electronic Warfare", 
                                                                                                    "98Y" = "(98Y) Signals Collector/Analyst", "98Z" = "(98Z) Signals Intelligence Electronic Warfare Senior Sergeant/Chief", "ZZZ" = "(ZZZ) Unknown MOS"),
                                                    data$RANK_PDE_GRP == "Warrant Officer" ~ dplyr::recode(data$MOS.CB, "001" = "(001) Unqualified in Authorized Warrant Officer MOS", "003" = "(003) Student", "004" = "(004) Duties Unassigned or in Transit", 
                                                                                                           "011" = "(011) Branch/MOS Immaterial", "131" = "(131) Field Artillery Targeting Technician", "140" = "(140) Air DefenseTechnician (RC)", "150" = "(150) Air Traffic Control Technician (RC)", 
                                                                                                           "151" = "(151) Aviation Maintenance Technician", "152" = "(152) Aviator", "153" = "(153) Aviator", "154" = "(154) Aviator", "155" = "(155) Aviator", "180" = "(180) Special Forces Warrant Officer", "210" = "(210) Utilities Operation and Maintenance Technician", 
                                                                                                           "215" = "(215) Geospatial Information Technician", "250" = "(250) Tactical Automated Network Technician", "251" = "(251) Air Defense Missile System Repair Technician NIKE", "254" = "(254) Signal Systems Support Technician", 
                                                                                                           "255" = "(255) Senior Signal Systems Technician", "270" = "(270) Legal Administrator", "311" = "(311) CID Special Agent", "350" = "(350) Intelligence Technician", "351" = "(351) Area Intelligence Technician", "352" = "(352) Non Morse Intercept Technician", 
                                                                                                           "353" = "(353) Intelligence Electronic Warfare (IEW) Systems Maintenance Techni", "420" = "(420) Military Personnel Technician", "550" = "(550) Legal Administrator", "640" = "(640) Veterinary Services Technician", "670" = "(670) Health Services Maintenance Technician", 
                                                                                                           "880" = "(880) Marine Deck Officer", "881" = "(881) Marine Engineering Officer", "882" = "(882) Mobility Officer", "890" = "(890) Ammunition Technician", "910" = "(910) Ammunition Warrant Officer", "912" = "(912) Land Combat Missile Systems Repair Technician", 
                                                                                                           "913" = "(913) Armament Repair Technician", "914" = "(914) Allied Trades Technician", "915" = "(915) Unit Maintenance Technician (Heavy)", "916" = "(916) High to Medium Altitude Air Defense (HIMAD) DS/GS Maintenance Te", 
                                                                                                           "917" = "(917) Maneuver Forces Air Defense Systems (MFADS) Technician", "918" = "(918) Electronic Systems Maintenance Warrant Officer", "919" = "(919) Engineer Equipment Repair Technician", "920" = "(920) Supply Systems Technician", 
                                                                                                           "921" = "(921) Airdrop Systems Technician", "922" = "(922) Food Service Technician", "948" = "(948) Electronic Systems Maintenance Warrant Officer", "ZZZ" = "(ZZZ) Unknown MOS"),
                                                    data$RANK_PDE_GRP == "Officer" ~ dplyr::recode(data$MOS.CB, "00A" = "(00A) Duties Unassigned", "00B" = "(00B) General Officer", "00D" = "(00D) Newly Commissioned Officers Awaiting Entry On Active Duty for Of", 
                                                                                                   "00E" = "(00E) Student Officer", "01A" = "(01A) Officer Generalist", "02A" = "(02A) Combat Arms Generalist", "03A" = "(03A) Infantry/Armor Immaterial", 
                                                                                                   "04A" = "(04A) Personnel Immaterial", "05A" = "(05A) Army Medical Department", "11A" = "(11A) Infantry", "12A" = "(12A) Armor General", "12B" = "(12B) Armor", 
                                                                                                   "12C" = "(12C) Cavalry", "13A" = "(13A) Field Artillery General", "14A" = "(14A) Air Defense Artillery General", "14B" = "(14B) Short Range Air Defense Artillery (SHORAD)", 
                                                                                                   "14D" = "(14D) HAWK Missile Air Defense Artillery", "14E" = "(14E) PATRIOT Missile Air Defense Artillery", "15A" = "(15A) Aviation General", 
                                                                                                   "15B" = "(15B) Aviation Combined Arms Operations", "15C" = "(15C) Aviation All Source Intelligence", "15D" = "(15D) Aviation Logistics", "15M" = "(15M) Aviation Combat Intelligence", 
                                                                                                   "18A" = "(18A) Special Forces", "19A" = "(19A) Armor General", "19B" = "(19B) Armor", "19C" = "(19C) Cavalry", "21A" = "(21A) Engineer General", "21B" = "(21B) Combat Engineer", 
                                                                                                   "21D" = "(21D) Facilities/Contract Construction Management Engineer (FCCME)", "24A" = "(24A) Telecommunications Systems Engineer", "24B" = "(24B) Data Systems Engineer", 
                                                                                                   "24Z" = "(24Z) Information Systems Engineer", "25A" = "(25A) Signal General", "25B" = "(25B) Communications Electronics Automation", "25C" = "(25C) Communications Electronics Operations", 
                                                                                                   "25D" = "(25D) Communications Electronics Engineering", "25E" = "(25E) Communications Electronics Networking", "27A" = "(27A) Judge Advocate General", 
                                                                                                   "27B" = "(27B) Military Judge", "30A" = "(30A) Information Operations Officer", "31A" = "(31A) Military Police", "34A" = "(34A) Strategic Intelligence Officer", 
                                                                                                   "35B" = "(35B) Strategic Intelligence (RC)", "35C" = "(35C) Imagery Intelligence", "35D" = "(35D) All Source Intelligence", "35E" = "(35E) Counterintelligence", 
                                                                                                   "35F" = "(35F) Human Intelligence", "35G" = "(35G) Signal Intelligence Electronic Warfare", "38A" = "(38A) Civil Affairs General (RC)", "39A" = "(39A) Psychological Operations or Civil Affairs General", 
                                                                                                   "39B" = "(39B) Psychological Operations", "39C" = "(39C) Civil Affairs", "39X" = "(39X) Psychological Operations and Civil Affairs Designated", "40A" = "(40A) Space Operations", 
                                                                                                   "41A" = "(41A) Personnel Programs Management Staff", "42A" = "(42A) Adjutant General General", "42B" = "(42B) Personnel Systems Management", "42C" = "(42C) Army Band", 
                                                                                                   "43A" = "(43A) Human Resources Management Officer", "44A" = "(44A) Finance General", "45A" = "(45A) Comptroller", "46A" = "(46A) Public Affairs General", "46B" = "(46B) Broadcast", 
                                                                                                   "47A" = "(47A) USMA Professor", "47C" = "(47C) USMA Professor of English", "47D" = "(47D) USMA Professor of Electrical Engineering and Computer Science", "47H" = "(47H) USMA Professor of Physics", 
                                                                                                   "47J" = "(47J) USMA Professor of Social Sciences", "47K" = "(47K) USMA Professor of History", "47L" = "(47L) USMA Professor of Behavioral Sciences and Leadership", 
                                                                                                   "47N" = "(47N) USMA Professor of Mathematical Sciences", "47P" = "(47P) USMA Professor of Geography and Environmental Engineering", "47Q" = "(47Q) USMA Professor and Associate Dean", 
                                                                                                   "47T" = "(47T) USMA Professor of Leader Development and Organizational Learning", "48B" = "(48B) Foreign Area Officer Latin America", "48C" = "(48C) Foreign Area Officer Europe", 
                                                                                                   "48D" = "(48D) Foreign Area Officer South Asia", "48E" = "(48E) Foreign Area Officer Eurasia", "48F" = "(48F) Foreign Area Officer China", "48G" = "(48G) Foreign Area Officer Mideast/North Africa", 
                                                                                                   "48H" = "(48H) Foreign Area Officer Northeast Asia", "48I" = "(48I) Foreign Area Officer South East Asia", "48J" = "(48J) Foreign Area Officer Africa South of Sahara", 
                                                                                                   "48X" = "(48X) Foreign Area Officer", "49A" = "(49A) Operations Research/Systems Analysis", "49D" = "(49D) Operations Research Planning Programming and Resource Management", 
                                                                                                   "49W" = "(49W) Trained Operations Research/System Analysis (ORSA)", "50A" = "(50A) Force Development Officer", "51A" = "(51A) Systems Development", "51C" = "(51C) Contract and Industrial Management", 
                                                                                                   "51R" = "(51R) Systems Automation Acquisition and Engineering", "51S" = "(51S) Research and Engineering", "51T" = "(51T) Test and Evaluation", "51Z" = "(51Z) Acquisition", 
                                                                                                   "52B" = "(52B) Nuclear and Counterproliferation", "53A" = "(53A) Information Systems Management", "53B" = "(53B) Systems Automation Engineering", "53X" = "(53X) Designated Systems Automation", 
                                                                                                   "54A" = "(54A) Operations Plans and Training", "55A" = "(55A) Judge Advocate General", "55B" = "(55B) Military Judge", "56A" = "(56A) Command and Unit Chaplain", 
                                                                                                   "57A" = "(57A) Simulations Operations Officer", "59A" = "(59A) Strategic Plans and Policy", "60A" = "(60A) Operational Medicine", "60B" = "(60B) Nuclear Medicine Officer", 
                                                                                                   "60C" = "(60C) Preventive Medicine Officer", "60D" = "(60D) Occupational Medicine Officer", "60F" = "(60F) Pulmonary Disease Officer", "60G" = "(60G) Gastroenterologist", 
                                                                                                   "60H" = "(60H) Cardiologist", "60J" = "(60J) Obstetrician and Gynecologist", "60K" = "(60K) Urologist", "60L" = "(60L) Dermatologist", "60M" = "(60M) Allergist/Clinical Immunologist", 
                                                                                                   "60N" = "(60N) Anesthesiologist", "60P" = "(60P) Pediatrician", "60Q" = "(60Q) Pediatric Cardiologist", "60R" = "(60R) Child Neurologist", "60S" = "(60S) Ophthalmologist", 
                                                                                                   "60T" = "(60T) Otolaryngologist", "60U" = "(60U) Child Psychiatrist", "60V" = "(60V) Neurologist", "60W" = "(60W) Psychiatrist", "61A" = "(61A) Nephrologist", "61B" = "(61B) Medical Oncologist/Hematologist", 
                                                                                                   "61C" = "(61C) Endocrinologist", "61D" = "(61D) Rheumatologist", "61E" = "(61E) Clinical Pharmacologist", "61F" = "(61F) Internist", "61G" = "(61G) Infectious Disease Officer", 
                                                                                                   "61H" = "(61H) Family Physician", "61J" = "(61J) General Surgeon", "61K" = "(61K) Thoracic Surgeon", "61L" = "(61L) Plastic Surgeon", "61M" = "(61M) Orthopedic Surgeon", "61N" = "(61N) Flight Surgeon", 
                                                                                                   "61P" = "(61P) Physiatrist", "61R" = "(61R) Diagnostic Radiologist", "61U" = "(61U) Pathologist", "61W" = "(61W) Peripheral Vascular Surgeon", "61Z" = "(61Z) Neurosurgeon", 
                                                                                                   "62A" = "(62A) Emergency Physician", "62B" = "(62B) Field Surgeon", "63A" = "(63A) General Dentist", "63B" = "(63B) Comprehensive Dentist", "63D" = "(63D) Periodontist", 
                                                                                                   "63E" = "(63E) Endodontist", "63F" = "(63F) Prosthodontist", "63K" = "(63K) Pediatric Dentist", "63M" = "(63M) Orthodontist", "63N" = "(63N) Oral and Maxillofacial Surgeon", 
                                                                                                   "63P" = "(63P) Oral Pathologist", "63R" = "(63R) Executive Dentist", "64A" = "(64A) Field Veterinary Service", "64B" = "(64B) Veterinary Staff Officer", "64D" = "(64D) Veterinary Pathology", 
                                                                                                   "64F" = "(64F) Veterinary Clinical Medicine", "64Z" = "(64Z) Senior Veterinarian (Immaterial)", "65A" = "(65A) Occupational Therapy", "65B" = "(65B) Physical Therapy", "65C" = "(65C) Dietitian", 
                                                                                                   "65D" = "(65D) Physician Assistant", "65X" = "(65X) Specialist Allied Operations", "66A" = "(66A) Nurse Administrator", "66B" = "(66B) Community Health Nurse", "66C" = "(66C) Psychiatric/Mental Health Nurse", 
                                                                                                   "66E" = "(66E) Perioperative Nurse", "66F" = "(66F) Nurse Anesthetist", "66G" = "(66G) Obstetrics and Gynecologic Nurse", "66H" = "(66H) Medical Surgical Nurse", "66N" = "(66N) Generalist Nurse", 
                                                                                                   "66P" = "(66P) Family Nurse Practitioner", "67A" = "(67A) Health Services", "67B" = "(67B) Laboratory Sciences", "67C" = "(67C) Preventive Medicine Sciences", "67D" = "(67D) Behavioral Sciences", 
                                                                                                   "67E" = "(67E) Pharmacy", "67F" = "(67F) Optometry", "67G" = "(67G) Podiatry", "67J" = "(67J) Aeromedical Evacuation", "70A" = "(70A) Health Care Administration", "70B" = "(70B) Health Services Administration", 
                                                                                                   "70C" = "(70C) Health Services Comptroller", "70D" = "(70D) Health Services Systems Management", "70E" = "(70E) Patient Administration", "70F" = "(70F) Health Services Human Resources", 
                                                                                                   "70H" = "(70H) Health Services Plans Operations Intelligence Security and Train", "70K" = "(70K) Health Services Materiel", "71A" = "(71A) Microbiology", "71B" = "(71B) Biochemistry", 
                                                                                                   "71E" = "(71E) Clinical Laboratory", "71F" = "(71F) Research Psychology", "72A" = "(72A) Nuclear Medical Science", "72B" = "(72B) Entomology", "72C" = "(72C) Audiology", 
                                                                                                   "72D" = "(72D) Environmental Science", "72E" = "(72E) Environmental Engineer", "73A" = "(73A) Social Work", "73B" = "(73B) Clinical Psychology", "74A" = "(74A) Chemical General", 
                                                                                                   "74B" = "(74B) Chemical Operations and Training", "74C" = "(74C) Chemical Munitions and Materiel Management", "88A" = "(88A) Transportation General", "88B" = "(88B) Traffic Management", 
                                                                                                   "88C" = "(88C) Marine and Terminal Operations", "88D" = "(88D) Motor/Rail Transportation", "88E" = "(88E) Transportation Management", "89E" = "(89E) Explosive Ordnance Disposal", 
                                                                                                   "90A" = "(90A) Logistics", "91A" = "(91A) Maintenance and Munitions Materiel Officer", "91B" = "(91B) Maintenance Management", "91D" = "(91D) Munitions Materiel Management", 
                                                                                                   "91E" = "(91E) Explosive Ordnance Disposal", "92A" = "(92A) Quartermaster General", "92B" = "(92B) Supply and Materiel Management", "92D" = "(92D) Aerial Delivery and Materiel", 
                                                                                                   "92F" = "(92F) Petroleum and Water", "97A" = "(97A) Contracting and Industrial Management Officer", "ZZZ" = "(ZZZ) Unknown MOS")))


## create MOS fields or branch [missing = 0.0244]
data$MOS.CB <- as.character(data$MOS.CB)
data$RANK_PDE_GRP <- as.character(data$RANK_PDE_GRP)
data <- data %>% dplyr::mutate(MOS_BRANCH = case_when(data$RANK_PDE_GRP == "Enlisted" ~ dplyr::recode(data$MOS.CB, "00B" = "EN", "00D" = "HQ", "00F" = "HQ", "00U" = "HQ", "00Z" = "HQ", "02A" = "AG", "02B" = "AG", "02C" = "AG", "02D" = "AG", 
                                                                                                      "02E" = "AG", "02F" = "AG", "02G" = "AG", "02H" = "AG", "02J" = "AG", "02K" = "AG", "02L" = "AG", "02M" = "AG", "02N" = "AG", "02T" = "AG", 
                                                                                                      "02U" = "AG", "02Z" = "AG", "09B" = "UN", "09C" = "UN", "09D" = "UN", "09L" = "UN", "09R" = "UN", "09S" = "UN", "09W" = "UN", "11B" = "IN", 
                                                                                                      "11C" = "IN", "11H" = "IN", "11M" = "IN", "11X" = "IN", "11Z" = "IN", "12B" = "EN", "12C" = "EN", "12Z" = "EN", "13B" = "FA", "13C" = "FA", 
                                                                                                      "13D" = "FA", "13E" = "FA", "13F" = "FA", "13M" = "FA", "13P" = "FA", "13R" = "FA", "13S" = "FA", "13W" = "FA", "13X" = "FA", "13Z" = "FA", 
                                                                                                      "14D" = "AD", "14E" = "AD", "14J" = "AD", "14M" = "AD", "14R" = "AD", "14S" = "AD", "14T" = "AD", "14Z" = "AD", "15B" = "AV", "15D" = "AV", 
                                                                                                      "15F" = "AV", "15G" = "AV", "15H" = "AV", "15J" = "AV", "15K" = "AV", "15M" = "AV", "15N" = "AV", "15P" = "AV", "15Q" = "AV", "15R" = "AV", 
                                                                                                      "15S" = "AV", "15T" = "AV", "15U" = "AV", "15V" = "AV", "15X" = "AV", "15Y" = "AV", "15Z" = "AV", "16F" = "AD", "18B" = "SF", "18C" = "SF", 
                                                                                                      "18D" = "SF", "18E" = "SF", "18F" = "SF", "18X" = "SF", "18Z" = "SF", "19D" = "AR", "19K" = "AR", "19Z" = "AR", "21B" = "EN", "21C" = "EN", 
                                                                                                      "21D" = "EN", "21E" = "EN", "21F" = "EN", "21G" = "EN", "21H" = "EN", "21J" = "EN", "21K" = "EN", "21L" = "EN", "21M" = "EN", "21N" = "EN", 
                                                                                                      "21P" = "EN", "21Q" = "EN", "21R" = "EN", "21S" = "EN", "21T" = "EN", "21U" = "EN", "21V" = "EN", "21W" = "EN", "21X" = "EN", "21Y" = "EN", 
                                                                                                      "21Z" = "EN", "24N" = "AD", "25B" = "SC", "25C" = "SC", "25D" = "SC", "25F" = "SC", "25L" = "SC", "25M" = "SC", "25P" = "SC", "25Q" = "SC", 
                                                                                                      "25R" = "SC", "25S" = "SC", "25T" = "SC", "25U" = "SC", "25V" = "SC", "25W" = "SC", "25X" = "SC", "25Y" = "SC", "25Z" = "SC", "27D" = "JA", 
                                                                                                      "27E" = "OD", "27M" = "OD", "27T" = "OD", "27X" = "OD", "27Z" = "OD", "31B" = "MP", "31C" = "SC", "31D" = "MP", "31E" = "MP", "31F" = "SC", 
                                                                                                      "31L" = "SC", "31M" = "SC", "31N" = "SC", "31P" = "SC", "31R" = "SC", "31S" = "SC", "31T" = "SC", "31U" = "SC", "31W" = "SC", "31Z" = "SC", 
                                                                                                      "33T" = "OD", "33W" = "OD", "33Z" = "OD", "35A" = "OD", "35B" = "OD", "35D" = "OD", "35E" = "OD", "35F" = "OD", "35H" = "OD", "35J" = "OD", 
                                                                                                      "35K" = "OD", "35L" = "OD", "35M" = "OD", "35N" = "OD", "35P" = "OD", "35Q" = "OD", "35R" = "OD", "35S" = "MD", "35T" = "MD", "35V" = "OD", 
                                                                                                      "35W" = "OD", "35Y" = "OD", "35Z" = "OD", "37F" = "PO", "38A" = "CA", "38B" = "CA", "39B" = "OD", "42A" = "AG", "42E" = "MD", "42F" = "AG", 
                                                                                                      "42L" = "AG", "42R" = "AG", "43M" = "QM", "44B" = "OD", "44C" = "OD", "44E" = "OD", "45B" = "OD", "45D" = "OD", "45E" = "OD", "45G" = "OD", 
                                                                                                      "45K" = "OD", "45N" = "OD", "45T" = "OD", "46Q" = "HQ", "46R" = "HQ", "46Z" = "HQ", "51B" = "EN", "51H" = "EN", "51K" = "EN", "51M" = "EN", 
                                                                                                      "51R" = "EN", "51T" = "EN", "51Z" = "EN", "52C" = "EN", "52D" = "EN", "52E" = "EN", "52G" = "EN", "52X" = "EN", "54B" = "CM", "55B" = "OD", 
                                                                                                      "55D" = "OD", "56M" = "CC", "57E" = "QM", "62B" = "EN", "62E" = "EN", "62F" = "EN", "62G" = "EN", "62H" = "EN", "62J" = "EN", "62N" = "EN", 
                                                                                                      "63A" = "OD", "63B" = "OD", "63D" = "OD", "63E" = "OD", "63G" = "OD", "63H" = "OD", "63J" = "OD", "63M" = "OD", "63N" = "OD", "63S" = "OD", 
                                                                                                      "63T" = "OD", "63W" = "OD", "63X" = "OD", "63Y" = "OD", "63Z" = "OD", "67G" = "AV", "67H" = "AV", "67N" = "AV", "67R" = "AV", "67S" = "AV", 
                                                                                                      "67T" = "AV", "67U" = "AV", "67V" = "AV", "67Y" = "AV", "67Z" = "AV", "68A" = "AV", "68B" = "AV", "68D" = "AV", "68E" = "AV", "68F" = "AV", 
                                                                                                      "68G" = "AV", "68H" = "AV", "68J" = "AV", "68K" = "AV", "68N" = "AV", "68P" = "AV", "68Q" = "AV", "68S" = "AV", "68W" = "AV", "68X" = "AV", 
                                                                                                      "68Y" = "AV", "68Z" = "AV", "71D" = "JA", "71G" = "MD", "71L" = "AG", "71M" = "CC", "73C" = "FI", "73D" = "FI", "73Z" = "FI", "74B" = "SC", 
                                                                                                      "74C" = "SC", "74D" = "SC", "74G" = "SC", "74Z" = "SC", "75B" = "AG", "75F" = "AG", "75H" = "AG", "75Z" = "AG", "76J" = "MD", "77F" = "QM", 
                                                                                                      "77L" = "QM", "77W" = "QM", "79R" = "HQ", "79S" = "HQ", "79T" = "HQ", "79V" = "HQ", "81L" = "EN", "81T" = "EN", "81Z" = "EN", "82C" = "FA", 
                                                                                                      "82D" = "EN", "88H" = "TC", "88K" = "TC", "88L" = "TC", "88M" = "TC", "88N" = "TC", "88P" = "TC", "88T" = "TC", "88U" = "TC", "88X" = "TC", 
                                                                                                      "88Z" = "TC", "89B" = "OD", "89D" = "OD", "91A" = "MD", "91B" = "MD", "91C" = "MD", "91D" = "MD", "91E" = "MD", "91G" = "MD", "91H" = "MD", 
                                                                                                      "91J" = "MD", "91K" = "MD", "91M" = "MD", "91P" = "MD", "91Q" = "MD", "91R" = "MD", "91S" = "MD", "91T" = "MD", "91V" = "MD", "91W" = "MD", 
                                                                                                      "91X" = "MD", "91Z" = "MD", "92A" = "QM", "92F" = "QM", "92G" = "QM", "92L" = "QM", "92M" = "QM", "92R" = "QM", "92S" = "QM", "92W" = "QM", 
                                                                                                      "92Y" = "QM", "92Z" = "QM", "93B" = "AV", "93C" = "AV", "93F" = "AV", "93P" = "AV", "94A" = "OD", "94D" = "OD", "94E" = "OD", "94F" = "OD", 
                                                                                                      "94H" = "OD", "94K" = "OD", "94L" = "OD", "94M" = "OD", "94P" = "OD", "94R" = "OD", "94S" = "OD", "94T" = "OD", "94W" = "OD", "94Y" = "OD", 
                                                                                                      "94Z" = "OD", "95B" = "MP", "95C" = "MP", "95D" = "MP", "96B" = "MI", "96D" = "MI", "96H" = "MI", "96R" = "MI", "96U" = "MI", "96Z" = "MI", 
                                                                                                      "97B" = "MI", "97E" = "MI", "97L" = "MI", "97Z" = "MI", "98C" = "MI", "98G" = "MI", "98H" = "MI", "98J" = "MI", "98K" = "MI", "98P" = "MI", 
                                                                                                      "98X" = "MI", "98Y" = "MI", "98Z" = "MI", "ZZZ" = "UN"),
                                                      data$RANK_PDE_GRP == "Warrant Officer" ~ dplyr::recode(data$MOS.CB, "001" = "UN", "003" = "UN", "004" = "UN", "011" = "UN", "131" = "FA", "140" = "AD", "150" = "AV", "151" = "AV", "152" = "AV", 
                                                                                                             "153" = "AV", "154" = "AV", "155" = "AV", "180" = "SF", "210" = "OD", "215" = "EN", "250" = "SC", "251" = "AD", "254" = "SC", "255" = "SC", 
                                                                                                             "270" = "JA", "311" = "MP", "350" = "MI", "351" = "MI", "352" = "MI", "353" = "MI", "420" = "MP", "550" = "JA", "640" = "MD", "670" = "MD", 
                                                                                                             "880" = "TC", "881" = "TC", "882" = "TC", "890" = "OD", "910" = "OD", "912" = "OD", "913" = "OD", "914" = "OD", "915" = "OD", "916" = "OD", 
                                                                                                             "917" = "OD", "918" = "OD", "919" = "OD", "920" = "QM", "921" = "QM", "922" = "QM", "948" = "OD", "ZZZ" = "UN"),
                                                      data$RANK_PDE_GRP == "Officer" ~ dplyr::recode(data$MOS.CB, "00A" = "UN", "00B" = "HQ", "00D" = "UN", "00E" = "UN", "01A" = "IN", "02A" = "IN", "03A" = "IN", "04A" = "UN", "05A" = "MD", "11A" = "IN", "12A" = "AR", "12B" = "AR", 
                                                                                                     "12C" = "AR", "13A" = "FA", "14A" = "AD", "14B" = "AD", "14D" = "AD", "14E" = "AD", "15A" = "AV", "15B" = "AV", "15C" = "AV", "15D" = "AV", "15M" = "AV", "18A" = "SF", 
                                                                                                     "19A" = "AR", "19B" = "AR", "19C" = "AR", "21A" = "EN", "21B" = "EN", "21D" = "EN", "24A" = "SC", "24B" = "SC", "24Z" = "SC", "25A" = "SC", "25B" = "SC", "25C" = "SC", 
                                                                                                     "25D" = "SC", "25E" = "SC", "27A" = "JA", "27B" = "JA", "30A" = "SC", "31A" = "MP", "34A" = "MI", "35B" = "MI", "35C" = "MI", "35D" = "MI", "35E" = "MI", "35F" = "MI", 
                                                                                                     "35G" = "MI", "38A" = "CA", "39A" = "PO", "39B" = "PO", "39C" = "CA", "39X" = "CA", "40A" = "HQ", "41A" = "AG", "42A" = "AG", "42B" = "AG", "42C" = "AG", "43A" = "AG", 
                                                                                                     "44A" = "FI", "45A" = "FI", "46A" = "HQ", "46B" = "HQ", "47A" = "HQ", "47C" = "HQ", "47D" = "HQ", "47H" = "HQ", "47J" = "HQ", "47K" = "HQ", "47L" = "HQ", "47N" = "HQ", 
                                                                                                     "47P" = "HQ", "47Q" = "HQ", "47T" = "HQ", "48B" = "HQ", "48C" = "HQ", "48D" = "HQ", "48E" = "HQ", "48F" = "HQ", "48G" = "HQ", "48H" = "HQ", "48I" = "HQ", "48J" = "HQ", 
                                                                                                     "48X" = "HQ", "49A" = "HQ", "49D" = "HQ", "49W" = "HQ", "50A" = "HQ", "51A" = "HQ", "51C" = "HQ", "51R" = "HQ", "51S" = "HQ", "51T" = "HQ", "51Z" = "HQ", "52B" = "HQ", 
                                                                                                     "53A" = "HQ", "53B" = "HQ", "53X" = "HQ", "54A" = "HQ", "55A" = "JA", "55B" = "JA", "56A" = "CC", "57A" = "HQ", "59A" = "HQ", "60A" = "MD", "60B" = "MD", "60C" = "MD", 
                                                                                                     "60D" = "MD", "60F" = "MD", "60G" = "MD", "60H" = "MD", "60J" = "MD", "60K" = "MD", "60L" = "MD", "60M" = "MD", "60N" = "MD", "60P" = "MD", "60Q" = "MD", "60R" = "MD", 
                                                                                                     "60S" = "MD", "60T" = "MD", "60U" = "MD", "60V" = "MD", "60W" = "MD", "61A" = "MD", "61B" = "MD", "61C" = "MD", "61D" = "MD", "61E" = "MD", "61F" = "MD", "61G" = "MD", 
                                                                                                     "61H" = "MD", "61J" = "MD", "61K" = "MD", "61L" = "MD", "61M" = "MD", "61N" = "MD", "61P" = "MD", "61R" = "MD", "61U" = "MD", "61W" = "MD", "61Z" = "MD", "62A" = "MD", 
                                                                                                     "62B" = "MD", "63A" = "MD", "63B" = "MD", "63D" = "MD", "63E" = "MD", "63F" = "MD", "63K" = "MD", "63M" = "MD", "63N" = "MD", "63P" = "MD", "63R" = "MD", "64A" = "MD", 
                                                                                                     "64B" = "MD", "64D" = "MD", "64F" = "MD", "64Z" = "MD", "65A" = "MD", "65B" = "MD", "65C" = "MD", "65D" = "MD", "65X" = "MD", "66A" = "MD", "66B" = "MD", "66C" = "MD", 
                                                                                                     "66E" = "MD", "66F" = "MD", "66G" = "MD", "66H" = "MD", "66N" = "MD", "66P" = "MD", "67A" = "MD", "67B" = "MD", "67C" = "MD", "67D" = "MD", "67E" = "MD", "67F" = "MD", 
                                                                                                     "67G" = "MD", "67J" = "MD", "70A" = "MD", "70B" = "MD", "70C" = "MD", "70D" = "MD", "70E" = "MD", "70F" = "MD", "70H" = "MD", "70K" = "MD", "71A" = "MD", "71B" = "MD", 
                                                                                                     "71E" = "MD", "71F" = "MD", "72A" = "MD", "72B" = "MD", "72C" = "MD", "72D" = "MD", "72E" = "MD", "73A" = "MD", "73B" = "MD", "74A" = "MD", "74B" = "MD", "74C" = "MD", 
                                                                                                     "88A" = "TC", "88B" = "TC", "88C" = "TC", "88D" = "TC", "88E" = "TC", "89E" = "OD", "90A" = "LC", "91A" = "OD", "91B" = "OD", "91D" = "OD", "91E" = "OD", "92A" = "QM", 
                                                                                                     "92B" = "QM", "92D" = "QM", "92F" = "QM", "97A" = "HQ", "ZZZ" = "UN")))

sort(unique(data$MOS_BRANCH))
# For MOS branch without mapping, change to 'unknown' UN
data$MOS_BRANCH[data$MOS_BRANCH %in% c("02S", "31V", "24T", "67D", "52L", "19E", "56D", "64E", "64C", "12N", "42S", "15W", "91L", "14G", "14H", "25N", "68T", "89A", "91F", "12M", "12W", "68M", "12D", "12Y", "12K", "36B", "68R", "35G", "12R", "13T", "12T", "15E", "36A",
                                       "12V", "21C", "61Q", "63H", "1",  "91C", "94B", "63F", "17D", "75C", "012", "29N", "12F", "16H", "17B", "36C", "76V", "16R", "88Y", "91M", "36M", "888", "52B", "31K", "98D", "52F", "FL",  "49C", "43E",
                                       "09E", "76W", "09T", "34H", "75E", "09W", "35A", "54B", "O9W", "38C", "52A", "68V", "11C", "38X", "16T", "37X", "71L", "00S", "13A", "37A", "36L", "76P", "76C", "16S", "75D", "57F", "55G", "29S", "29J",
                                       "39L", "39E", "16P", "29E", "01H", "91Y", "76Y", "31Y", "16D", "35U", "16E", "93D", "92B", "48A", "29Y", "33Y", "27H", "68L", "97G", "16B", "74F", "51G", "45L", "83F", "76X", "33R", "27B", "29V", "13N",
                                       "42D", "13E", "92G", "09G", "09N", "71T", "68A", "42H", "00R", "00G", "92Y", "09Q", "35X", "91W", "25E", "12H", "120", "31B", "68C", "66R", "68U", "09R", "66W", "56X", "290", "11B", "17A", "17C", "17X",
                                       "12X", "14P", "88M", "66S", "91J", "19D", "13J", "09S", "94F", "66T", "92S", "68E", "68W", "56M", "09U", "12J", "25B", "170", "46S", "125", "17E", "26A", "25U", "63S", "25S", "89B")
] <- "UN"

## MOS Type [missing = 0.00076]
# derived from PDE lookup table 'LKUP_ARMY_MOS' (CA = combat arms, CS = combat support, CSS = combat service support, SPEC = special service, OPS = operations, UNK = unknown)
data$MOS.CB <- as.character(data$MOS.CB)
data$RANK_PDE_GRP <- as.character(data$RANK_PDE_GRP)
data <- data %>% dplyr::mutate(MOS_TYPE = case_when(data$RANK_PDE_GRP == "Enlisted" ~ dplyr::recode(data$MOS.CB, "00B" = "CA", "00D" = "OPS", "00F" = "OPS", "00U" = "OPS", "00Z" = "OPS", 
                                                                                                    "02A" = "CSS", "02B" = "CSS", "02C" = "CSS", "02D" = "CSS", "02E" = "CSS", "02F" = "CSS", "02G" = "CSS", "02H" = "CSS", "02J" = "CSS", "02K" = "CSS", "02L" = "CSS", 
                                                                                                    "02M" = "CSS", "02N" = "CSS", "02T" = "CSS", "02U" = "CSS", "02Z" = "CSS", "09B" = "UNK", "09C" = "UNK", "09D" = "UNK", "09L" = "UNK", "09R" = "UNK", "09S" = "UNK", 
                                                                                                    "09W" = "UNK", "11B" = "CA", "11C" = "CA", "11H" = "CA", "11M" = "CA", "11X" = "CA", "11Z" = "CA", "12B" = "CA", "12C" = "CA", "12Z" = "CA", "13B" = "CA", "13C" = "CA", 
                                                                                                    "13D" = "CA", "13E" = "CA", "13F" = "CA", "13M" = "CA", "13P" = "CA", "13R" = "CA", "13S" = "CA", "13W" = "CA", "13X" = "CA", "13Z" = "CA", "14D" = "CA", "14E" = "CA", 
                                                                                                    "14J" = "CA", "14M" = "CA", "14R" = "CA", "14S" = "CA", "14T" = "CA", "14Z" = "CA", "15B" = "CA", "15D" = "CA", "15F" = "CA", "15G" = "CA", "15H" = "CA", "15J" = "CA", 
                                                                                                    "15K" = "CA", "15M" = "CA", "15N" = "CA", "15P" = "CA", "15Q" = "CA", "15R" = "CA", "15S" = "CA", "15T" = "CA", "15U" = "CA", "15V" = "CA", "15X" = "CA", "15Y" = "CA", 
                                                                                                    "15Z" = "CA", "16F" = "CA", "18B" = "CA", "18C" = "CA", "18D" = "CA", "18E" = "CA", "18F" = "CA", "18X" = "CA", "18Z" = "CA", "19D" = "CA", "19K" = "CA", "19Z" = "CA", 
                                                                                                    "21B" = "CA", "21C" = "CA", "21D" = "CA", "21E" = "CA", "21F" = "CA", "21G" = "CA", "21H" = "CA", "21J" = "CA", "21K" = "CA", "21L" = "CA", "21M" = "CA", "21N" = "CA", 
                                                                                                    "21P" = "CA", "21Q" = "CA", "21R" = "CA", "21S" = "CA", "21T" = "CA", "21U" = "CA", "21V" = "CA", "21W" = "CA", "21X" = "CA", "21Y" = "CA", "21Z" = "CA", "24N" = "CA", 
                                                                                                    "25B" = "CS", "25C" = "CS", "25D" = "CS", "25F" = "CS", "25L" = "CS", "25M" = "CS", "25P" = "CS", "25Q" = "CS", "25R" = "CS", "25S" = "CS", "25T" = "CS", "25U" = "CS", 
                                                                                                    "25V" = "CS", "25W" = "CS", "25X" = "CS", "25Y" = "CS", "25Z" = "CS", "27D" = "SPEC", "27E" = "CSS", "27M" = "CSS", "27T" = "CSS", "27X" = "CSS", "27Z" = "CSS", "31B" = "CS", 
                                                                                                    "31C" = "CS", "31D" = "CS", "31E" = "CS", "31F" = "CS", "31L" = "CS", "31M" = "CS", "31N" = "CS", "31P" = "CS", "31R" = "CS", "31S" = "CS", "31T" = "CS", "31U" = "CS", 
                                                                                                    "31W" = "CS", "31Z" = "CS", "33T" = "CSS", "33W" = "CSS", "33Z" = "CSS", "35A" = "CSS", "35B" = "CSS", "35D" = "CSS", "35E" = "CSS", "35F" = "CSS", "35H" = "CSS", 
                                                                                                    "35J" = "CSS", "35K" = "CSS", "35L" = "CSS", "35M" = "CSS", "35N" = "CSS", "35P" = "CSS", "35Q" = "CSS", "35R" = "CSS", "35S" = "SPEC", "35T" = "SPEC", "35V" = "CSS", 
                                                                                                    "35W" = "CSS", "35Y" = "CSS", "35Z" = "CSS", "37F" = "OPS", "38A" = "CS", "38B" = "CS", "39B" = "CSS", "42A" = "CSS", "42E" = "SPEC", "42F" = "CSS", "42L" = "CSS", 
                                                                                                    "42R" = "CSS", "43M" = "CSS", "44B" = "CSS", "44C" = "CSS", "44E" = "CSS", "45B" = "CSS", "45D" = "CSS", "45E" = "CSS", "45G" = "CSS", "45K" = "CSS", "45N" = "CSS", 
                                                                                                    "45T" = "CSS", "46Q" = "OPS", "46R" = "OPS", "46Z" = "OPS", "51B" = "CA", "51H" = "CA", "51K" = "CA", "51M" = "CA", "51R" = "CA", "51T" = "CA", "51Z" = "CA", "52C" = "CA", 
                                                                                                    "52D" = "CA", "52E" = "CA", "52G" = "CA", "52X" = "CA", "54B" = "CS", "55B" = "CSS", "55D" = "CSS", "56M" = "SPEC", "57E" = "CSS", "62B" = "CA", "62E" = "CA", "62F" = "CA", 
                                                                                                    "62G" = "CA", "62H" = "CA", "62J" = "CA", "62N" = "CA", "63A" = "CSS", "63B" = "CSS", "63D" = "CSS", "63E" = "CSS", "63G" = "CSS", "63H" = "CSS", "63J" = "CSS", "63M" = "CSS", 
                                                                                                    "63N" = "CSS", "63S" = "CSS", "63T" = "CSS", "63W" = "CSS", "63X" = "CSS", "63Y" = "CSS", "63Z" = "CSS", "67G" = "CA", "67H" = "CA", "67N" = "CA", "67R" = "CA", "67S" = "CA", 
                                                                                                    "67T" = "CA", "67U" = "CA", "67V" = "CA", "67Y" = "CA", "67Z" = "CA", "68A" = "CA", "68B" = "CA", "68D" = "CA", "68E" = "CA", "68F" = "CA", "68G" = "CA", "68H" = "CA", 
                                                                                                    "68J" = "CA", "68K" = "CA", "68N" = "CA", "68P" = "CA", "68Q" = "CA", "68S" = "CA", "68W" = "CA", "68X" = "CA", "68Y" = "CA", "68Z" = "CA", "71D" = "SPEC", "71G" = "SPEC", 
                                                                                                    "71L" = "CSS", "71M" = "SPEC", "73C" = "CSS", "73D" = "CSS", "73Z" = "CSS", "74B" = "CS", "74C" = "CS", "74D" = "CS", "74G" = "CS", "74Z" = "CS", "75B" = "CSS", "75F" = "CSS", 
                                                                                                    "75H" = "CSS", "75Z" = "CSS", "76J" = "SPEC", "77F" = "CSS", "77L" = "CSS", "77W" = "CSS", "79R" = "OPS", "79S" = "OPS", "79T" = "OPS", "79V" = "OPS", "81L" = "CA", 
                                                                                                    "81T" = "CA", "81Z" = "CA", "82C" = "CA", "82D" = "CA", "88H" = "CSS", "88K" = "CSS", "88L" = "CSS", "88M" = "CSS", "88N" = "CSS", "88P" = "CSS", "88T" = "CSS", "88U" = "CSS", 
                                                                                                    "88X" = "CSS", "88Z" = "CSS", "89B" = "CSS", "89D" = "CSS", "91A" = "SPEC", "91B" = "SPEC", "91C" = "SPEC", "91D" = "SPEC", "91E" = "SPEC", "91G" = "SPEC", "91H" = "SPEC", 
                                                                                                    "91J" = "SPEC", "91K" = "SPEC", "91M" = "SPEC", "91P" = "SPEC", "91Q" = "SPEC", "91R" = "SPEC", "91S" = "SPEC", "91T" = "SPEC", "91V" = "SPEC", "91W" = "SPEC", "91X" = "SPEC", 
                                                                                                    "91Z" = "SPEC", "92A" = "CSS", "92F" = "CSS", "92G" = "CSS", "92L" = "CSS", "92M" = "CSS", "92R" = "CSS", "92S" = "CSS", "92W" = "CSS", "92Y" = "CSS", "92Z" = "CSS", 
                                                                                                    "93B" = "CA", "93C" = "CA", "93F" = "CA", "93P" = "CA", "94A" = "CSS", "94D" = "CSS", "94E" = "CSS", "94F" = "CSS", "94H" = "CSS", "94K" = "CSS", "94L" = "CSS", "94M" = "CSS", 
                                                                                                    "94P" = "CSS", "94R" = "CSS", "94S" = "CSS", "94T" = "CSS", "94W" = "CSS", "94Y" = "CSS", "94Z" = "CSS", "95B" = "CS", "95C" = "CS", "95D" = "CS", "96B" = "CS", "96D" = "CS", 
                                                                                                    "96H" = "CS", "96R" = "CS", "96U" = "CS", "96Z" = "CS", "97B" = "CS", "97E" = "CS", "97L" = "CS", "97Z" = "CS", "98C" = "CS", "98G" = "CS", "98H" = "CS", "98J" = "CS", 
                                                                                                    "98K" = "CS", "98P" = "CS", "98X" = "CS", "98Y" = "CS", "98Z" = "CS", "ZZZ" = "UNK"),
                                                    data$RANK_PDE_GRP == "Warrant Officer" ~ dplyr::recode(data$MOS.CB, "001" = "UNK", "003" = "UNK", "004" = "UNK", "011" = "UNK", "131" = "CA", 
                                                                                                           "140" = "CA", "150" = "CA", "151" = "CA", "152" = "CA", "153" = "CA", "154" = "CA", "155" = "CA", "180" = "CA", "210" = "CSS", "215" = "CA", "250" = "CS", 
                                                                                                           "251" = "CA", "254" = "CA", "255" = "CA", "270" = "SPEC", "311" = "CS", "350" = "CS", "351" = "CS", "352" = "CS", "353" = "CS", "420" = "CS", "550" = "SPEC", 
                                                                                                           "640" = "SPEC", "670" = "SPEC", "880" = "CSS", "881" = "CSS", "882" = "CSS", "890" = "CSS", "910" = "CSS", "912" = "CSS", "913" = "CSS", "914" = "CSS", 
                                                                                                           "915" = "CSS", "916" = "CSS", "917" = "CSS", "918" = "CSS", "919" = "CSS", "920" = "CSS", "921" = "CSS", "922" = "CSS", "948" = "CSS", "ZZZ" = "UNK"),
                                                    data$RANK_PDE_GRP == "Officer" ~ dplyr::recode(data$MOS.CB, "00A" = "UNK", "00B" = "OPS", "00D" = "UNK", "00E" = "UNK", "01A" = "CA", 
                                                                                                   "02A" = "CA", "03A" = "CA", "04A" = "UNK", "05A" = "SPEC", "11A" = "CA", "12A" = "CA", "12B" = "CA", "12C" = "CA", "13A" = "CA", "14A" = "CA", "14B" = "CA", 
                                                                                                   "14D" = "CA", "14E" = "CA", "15A" = "CA", "15B" = "CA", "15C" = "CA", "15D" = "CA", "15M" = "CA", "18A" = "CA", "19A" = "CA", "19B" = "CA", "19C" = "CA", 
                                                                                                   "21A" = "CA", "21B" = "CA", "21D" = "CA", "24A" = "CS", "24B" = "CS", "24Z" = "CS", "25A" = "CS", "25B" = "CS", "25C" = "CS", "25D" = "CS", "25E" = "CS", 
                                                                                                   "27A" = "SPEC", "27B" = "SPEC", "30A" = "CS", "31A" = "CS", "34A" = "CS", "35B" = "CS", "35C" = "CS", "35D" = "CS", "35E" = "CS", "35F" = "CS", "35G" = "CS", 
                                                                                                   "38A" = "CS", "39A" = "OPS", "39B" = "OPS", "39C" = "CS", "39X" = "OPS", "40A" = "OPS", "41A" = "CSS", "42A" = "CSS", "42B" = "CSS", "42C" = "CSS", "43A" = "CSS", 
                                                                                                   "44A" = "CSS", "45A" = "CSS", "46A" = "OPS", "46B" = "OPS", "47A" = "OPS", "47C" = "OPS", "47D" = "OPS", "47H" = "OPS", "47J" = "OPS", "47K" = "OPS", "47L" = "OPS", 
                                                                                                   "47N" = "OPS", "47P" = "OPS", "47Q" = "OPS", "47T" = "OPS", "48B" = "OPS", "48C" = "OPS", "48D" = "OPS", "48E" = "OPS", "48F" = "OPS", "48G" = "OPS", "48H" = "OPS", 
                                                                                                   "48I" = "OPS", "48J" = "OPS", "48X" = "OPS", "49A" = "OPS", "49D" = "OPS", "49W" = "OPS", "50A" = "OPS", "51A" = "OPS", "51C" = "OPS", "51R" = "OPS", "51S" = "OPS", 
                                                                                                   "51T" = "OPS", "51Z" = "OPS", "52B" = "OPS", "53A" = "OPS", "53B" = "OPS", "53X" = "OPS", "54A" = "OPS", "55A" = "SPEC", "55B" = "SPEC", "56A" = "SPEC", "57A" = "OPS", 
                                                                                                   "59A" = "OPS", "60A" = "SPEC", "60B" = "SPEC", "60C" = "SPEC", "60D" = "SPEC", "60F" = "SPEC", "60G" = "SPEC", "60H" = "SPEC", "60J" = "SPEC", "60K" = "SPEC", 
                                                                                                   "60L" = "SPEC", "60M" = "SPEC", "60N" = "SPEC", "60P" = "SPEC", "60Q" = "SPEC", "60R" = "SPEC", "60S" = "SPEC", "60T" = "SPEC", "60U" = "SPEC", "60V" = "SPEC", 
                                                                                                   "60W" = "SPEC", "61A" = "SPEC", "61B" = "SPEC", "61C" = "SPEC", "61D" = "SPEC", "61E" = "SPEC", "61F" = "SPEC", "61G" = "SPEC", "61H" = "SPEC", "61J" = "SPEC", 
                                                                                                   "61K" = "SPEC", "61L" = "SPEC", "61M" = "SPEC", "61N" = "SPEC", "61P" = "SPEC", "61R" = "SPEC", "61U" = "SPEC", "61W" = "SPEC", "61Z" = "SPEC", "62A" = "SPEC", 
                                                                                                   "62B" = "SPEC", "63A" = "SPEC", "63B" = "SPEC", "63D" = "SPEC", "63E" = "SPEC", "63F" = "SPEC", "63K" = "SPEC", "63M" = "SPEC", "63N" = "SPEC", "63P" = "SPEC", 
                                                                                                   "63R" = "SPEC", "64A" = "SPEC", "64B" = "SPEC", "64D" = "SPEC", "64F" = "SPEC", "64Z" = "SPEC", "65A" = "SPEC", "65B" = "SPEC", "65C" = "SPEC", "65D" = "SPEC", 
                                                                                                   "65X" = "SPEC", "66A" = "SPEC", "66B" = "SPEC", "66C" = "SPEC", "66E" = "SPEC", "66F" = "SPEC", "66G" = "SPEC", "66H" = "SPEC", "66N" = "SPEC", "66P" = "SPEC", 
                                                                                                   "67A" = "SPEC", "67B" = "SPEC", "67C" = "SPEC", "67D" = "SPEC", "67E" = "SPEC", "67F" = "SPEC", "67G" = "SPEC", "67J" = "SPEC", "70A" = "SPEC", "70B" = "SPEC", 
                                                                                                   "70C" = "SPEC", "70D" = "SPEC", "70E" = "SPEC", "70F" = "SPEC", "70H" = "SPEC", "70K" = "SPEC", "71A" = "SPEC", "71B" = "SPEC", "71E" = "SPEC", "71F" = "SPEC", 
                                                                                                   "72A" = "SPEC", "72B" = "SPEC", "72C" = "SPEC", "72D" = "SPEC", "72E" = "SPEC", "73A" = "SPEC", "73B" = "SPEC", "74A" = "SPEC", "74B" = "SPEC", "74C" = "SPEC", 
                                                                                                   "88A" = "CSS", "88B" = "CSS", "88C" = "CSS", "88D" = "CSS", "88E" = "CSS", "89E" = "CSS", "90A" = "OPS", "91A" = "CSS", "91B" = "CSS", "91D" = "CSS", "91E" = "CSS", 
                                                                                                   "92A" = "CSS", "92B" = "CSS", "92D" = "CSS", "92F" = "CSS", "97A" = "OPS", "ZZZ" = "UNK")))

sort(unique(data$MOS_TYPE))
# For MOS type without mapping, change to 'unknown' ZZ
data$MOS_TYPE[data$MOS_TYPE %in% c("001", "003", "004", "00A", "00E", "00G", "00R", "00S", "012", "01A", "01H", "02S", "03A", "09E", "09G", "09N", "09Q", "09T", "09U", "1", "11A", "120", "125", "12A", "12D", "12F", "12H", "12J", 
                                   "12K", "12M", "12N", "12R", "12T", "12V", "12W", "12X", "12Y", "131", "13A", "13J", "13N", "13T", "140", "14A", "14B", "14G", "14H", "14P", "150", "151", "152", "153", "154", "155", "15A", "15C", 
                                   "15E", "15W", "16B", "16D", "16E", "16H", "16P", "16R", "16S", "16T", "170", "17A", "17B", "17C", "17D", "17E", "17X", "180", "18A", "19A", "19B", "19C", "19E", "210", "215", "21A", "24A", "24B", 
                                   "24T", "24Z", "250", "251", "254", "255", "25A", "25E", "25N", "26A", "270", "27A", "27B", "27H", "290", "29E", "29J", "29N", "29S", "29V", "29Y", "30A", "311", "31A", "31K", "31V", "31Y", "33R", 
                                   "33Y", "34A", "34H", "350", "351", "352", "353", "35C", "35G", "35U", "35X", "36A", "36B", "36C", "36L", "36M", "37A", "37X", "38C", "38X", "39A", "39C", "39E", "39L", "40A", "420", "42B", "42C", 
                                   "42D", "42H", "42S", "43A", "43E", "44A", "45A", "45L", "46A", "46B", "46S", "48A", "48B", "48C", "48D", "48E", "48F", "48G", "48H", "48I", "48J", "48X", "49A", "49C", "50A", "51A", "51C", "51G", 
                                   "51S", "52A", "52B", "52F", "52L", "53A", "54A", "550", "55A", "55G", "56A", "56D", "56X", "57A", "57F", "59A", "60A", "60B", "60C", "60D", "60F", "60G", "60H", "60J", "60K", "60L", "60M", "60N", 
                                   "60P", "60Q", "60R", "60S", "60T", "60U", "60V", "60W", "61A", "61B", "61C", "61D", "61E", "61F", "61G", "61H", "61J", "61K", "61L", "61M", "61N", "61P", "61Q", "61R", "61U", "61W", "61Z", "62A", 
                                   "63F", "63K", "63P", "640", "64A", "64B", "64C", "64D", "64E", "64F", "65A", "65B", "65C", "65D", "66A", "66B", "66C", "66E", "66F", "66G", "66H", "66N", "66P", "66R", "66S", "66T", "66W", "670",
                                   "67A", "67B", "67C", "67D", "67E", "67F", "67J", "68C", "68L", "68M", "68R", "68T", "68U", "68V", "70A", "70B", "70C", "70D", "70E", "70F", "70H", "70K", "71A", "71B", "71E", "71F", "71T", "72A", 
                                   "72B", "72C", "72D", "72E", "73A", "73B", "74A", "74F", "75C", "75D", "75E", "76C", "76P", "76V", "76W", "76X", "76Y", "83F", "880", "881", "882", "888", "88A", "88B", "88C", "88D", "88Y", "890", 
                                   "89A", "89E", "90A", "910", "912", "913", "914", "915", "916", "917", "918", "919", "91F", "91L", "91Y", "920", "921", "922", "92B", "92D", "93D", "948", "94B", "97A", "97G", "98D", "FL", "O9W")
] <- "UNK" 

## First duty base location [missing = 0.503]
data$DTY_BASE_FAC_ID <- as.character(data$DTY_BASE_FAC_ID)
data <- data %>% dplyr::mutate(DTY_BASE_NAME = dplyr::recode(data$DTY_BASE_FAC_ID, "01001A" = "(01001A) Alabama Army Ammunition Plant Childersburg", "01002A" = "(01002A) Anniston Army Depot", "01006A" = "(01006A) Fort McClellan", 
                                                             "01007A" = "(01007A) Fort Rucker", "01013A" = "(01013A) Redstone Arsenal Huntsville", "02006A" = "(02006A) Fort Jonathan Wainwright Fairbanks", "02007A" = "(02007A) Fort Richardson", 
                                                             "04003A" = "(04003A) Fort Huachuca", "04005A" = "(04005A) Navajo Army Depot Activity Bellemont", "04010A" = "(04010A) Yuma Proving Ground", "05005A" = "(05005A) Pine Bluff Arsenal", 
                                                             "06021A" = "(06021A) Fort Irwin", "06022A" = "(06022A) Fort MacArthur San Pedro", "06023A" = "(06023A) Fort Ord", "06026A" = "(06026A) Hamilton Field", 
                                                             "06031A" = "(06031A) Los Alamitos Army Reserve Center Rossmoor", "06046A" = "(06046A) Oakland Army Base", "06056A" = "(06056A) Presidio of Monterey", "06057A" = "(06057A) Presidio of San Francisco", 
                                                             "06058A" = "(06058A) Riverbank Army Ammunition Plant", "06059A" = "(06059A) Sacramento Army Depot", "06070A" = "(06070A) Sharpe Army Depot Lathrop", "06071A" = "(06071A) Sierra Army Depot Herlong", 
                                                             "08003A" = "(08003A) Fitzsimons Army Medical Center Aurora", "08004A" = "(08004A) Fort Carson", "08005A" = "(08005A) Fort Collins Denver", "08009A" = "(08009A) Pueblo Army Depot Activity", 
                                                             "08010A" = "(08010A) Rocky Mountain Arsenal Adams City", "09002A" = "(09002A) Fort Nathan Hale East Haven", "11004A" = "(11004A) Fort Leslie J McNair", 
                                                             "11007A" = "(11007A) Walter Reed Army Medical Center Washington", "12001A" = "(12001A) Camp Blanding Starke", "12005A" = "(12005A) Fort Myers", 
                                                             "12019A" = "(12019A) Simulation Training and Instrumentation Command Orlando", "13004A" = "(13004A) Fort Benning Columbus", "13005A" = "(13005A) Fort Gillem Forest Park", 
                                                             "13006A" = "(13006A) Fort Gordon", "13007A" = "(13007A) Fort McPherson", "13008A" = "(13008A) Fort Stewart", "13009A" = "(13009A) Fort Valley", "15003A" = "(15003A) Fort Shafter Honolulu", 
                                                             "16002A" = "(16002A) Gowen Field Boise", "17002A" = "(17002A) Charles Melvin Price Center Mitchell", "17003A" = "(17003A) Fort Sheridan", "17007A" = "(17007A) Joliet Army Ammunition Plant Elwood", 
                                                             "17009A" = "(17009A) Rock Island Arsenal", "17010A" = "(17010A) Savanna Army Depot Activity", "18003A" = "(18003A) Fort Benjamin Harrison", "18007A" = "(18007A) Indiana Army Ammunition Plant Charlestown", 
                                                             "18009A" = "(18009A) Jefferson Proving Ground Madison", "18011A" = "(18011A) Newport Army Ammunition Plant", "19002A" = "(19002A) Fort Des Moines", "19004A" = "(19004A) Fort Snelling Fort Dodge", 
                                                             "19005A" = "(19005A) Iowa Army Ammunition Plant Middletown", "20004A" = "(20004A) Fort Leavenworth", "20005A" = "(20005A) Fort Riley", "20006A" = "(20006A) Kansas Army Ammunition Plant Parsons", 
                                                             "20008A" = "(20008A) Sunflower Army Ammunition Plant DeSoto", "21001A" = "(21001A) Fort Campbell", "21002A" = "(21002A) Fort Knox", "21003A" = "(21003A) Lexington Blue Grass Depot", 
                                                             "22006A" = "(22006A) Fort Polk", "22008A" = "(22008A) Louisiana Army Ammunition Plant Shreveport", "22009A" = "(22009A) New Orleans Military Ocean Terminal", "24001A" = "(24001A) Aberdeen Proving Ground", 
                                                             "24005A" = "(24005A) Fort Detrick Lewistown", "24006A" = "(24006A) Fort George G Meade", "24007A" = "(24007A) Fort Ritchie", "24008A" = "(24008A) Harry Diamond Laboratories Chillum", 
                                                             "25003A" = "(25003A) Camp Edwards (Army National Guard) Bourne", "25005A" = "(25005A) Fort Devens", "25007A" = "(25007A) Natick Army Research and Development Center", 
                                                             "25011A" = "(25011A) South Boston Army Reserve Center", "25013A" = "(25013A) Watertown Army Materiel and Technical Center", "26002A" = "(26002A) Detroit Arsenal Warren", 
                                                             "26004A" = "(26004A) Fort Custer Training Center Augusta", "26006A" = "(26006A) Michigan Army Missile Plant Sterling Heights", "27002A" = "(27002A) Camp Ripley Little Falls", 
                                                             "27007A" = "(27007A) Twin Cities Army Ammunition Plant New Brighton", "28002A" = "(28002A) Camp McCain (Army National Guard) Elliott", "28003A" = "(28003A) Camp Shelby Hattiesburg", 
                                                             "28009A" = "(28009A) Mississippi Army Ammunition Plant Picayune", "29003A" = "(29003A) Aviation and Troop Command St Louis", "29005A" = "(29005A) Fort Leonard Wood", 
                                                             "29006A" = "(29006A) Gateway Army Ammunition Plant Maplewood", "29008A" = "(29008A) Lake City Army Ammunition Plant Independence", "30001A" = "(30001A) Fort Missoula Army Reserve Center", 
                                                             "30002A" = "(30002A) Fort William H Harrison Helena", "31001A" = "(31001A) Cornhusker Army Ammunition Plant Grand Island", "31003A" = "(31003A) National Guard Mead Facility", 
                                                             "33001A" = "(33001A) Army Cold Regions Research Laboratory Hanover", "34002A" = "(34002A) Fort Dix", "34003A" = "(34003A) Fort Monmouth", "34007A" = "(34007A) Picatinny Arsenal Dover", 
                                                             "35003A" = "(35003A) Fort Wingate Depot Activity Gallup", "35006A" = "(35006A) White Sands Missile Range", "36007A" = "(36007A) Fort Drum", "36008A" = "(36008A) Galeville Training Site Wallkill", 
                                                             "36017A" = "(36017A) Seneca Army Depot Romulus", "36023A" = "(36023A) Watervliet Arsenal", "36024A" = "(36024A) West Point Military Reservation", "37008A" = "(37008A) Fort Bragg", 
                                                             "37011A" = "(37011A) Oak Ridge Army Reserve Center", "37014A" = "(37014A) Sunnypoint Military Ocean Terminal Long Beach", "37015A" = "(37015A) Tarheel Army Missile Plant Glen Raven", 
                                                             "39007A" = "(39007A) Erie Army Depot Camp Perry Port Clinton", "39008A" = "(39008A) Lima Army Tank Center", "39012A" = "(39012A) Ravenna Army Ammunition Plant", "40003A" = "(40003A) Fort Sill", 
                                                             "40004A" = "(40004A) McAlester Army Ammunition Plant", "41005A" = "(41005A) Umatilla Depot Stayton", "42002A" = "(42002A) Carlisle Barracks", "42003A" = "(42003A) Charles Kelly Support Facility Noblestown", 
                                                             "42007A" = "(42007A) Letterkenny Army Depot Chambersburg", "42009A" = "(42009A) New Cumberland Army Depot", "42015A" = "(42015A) Scranton Army Ammunition Plant", "45006A" = "(45006A) Fort Jackson", 
                                                             "47003A" = "(47003A) Holston Army Ammunition Plant Kingsport", "47009A" = "(47009A) Milan Army Ammunition Plant", "47012A" = "(47012A) Volunteer Army Ammunition Plant Chattanooga", 
                                                             "48004A" = "(48004A) Camp Swift Bastrop", "48007A" = "(48007A) Corpus Christi Army Depot", "48011A" = "(48011A) Fort Bliss", "48012A" = "(48012A) Fort Hood", "48013A" = "(48013A) Fort Sam Houston San Antonio", 
                                                             "48014A" = "(48014A) Fort Worth Army Reserve Center", "48022A" = "(48022A) Longhorn Army Ammunition Plant Marshall", "48028A" = "(48028A) Red River Depot Wake Village", 
                                                             "49002A" = "(49002A) Camp W G Williams Riverton", "49006A" = "(49006A) Tooele Army Depot", "50002A" = "(50002A) Ethan Allen Facility Jericho", "51002A" = "(51002A) Arlington Hall Station", 
                                                             "51008A" = "(51008A) Department of the Army Activities Pentagon", "51010A" = "(51010A) Fort Belvoir", "51011A" = "(51011A) Fort Eustis", "51012A" = "(51012A) Fort Lee", 
                                                             "51013A" = "(51013A) Fort Monroe Hampton", "51014A" = "(51014A) Fort Myer", "51015A" = "(51015A) Fort Story", "51025A" = "(51025A) Radford Army Ammunition Plant", "51029A" = "(51029A) Vint Hill Farms Station", 
                                                             "53006A" = "(53006A) Fort Lawton Seattle", "53007A" = "(53007A) Fort Lewis", "53014A" = "(53014A) Vancouver Barracks", "55001A" = "(55001A) Badger Army Ammunition Plant Baraboo", 
                                                             "55002A" = "(55002A) Camp Douglas", "55003A" = "(55003A) Fort McCoy Sparta", "56002A" = "(56002A) Camp Guernsey", "67001A" = "(67001A) Johnston Atoll", "BE001A" = "(BE001A) Chievres Army Station", 
                                                             "BE002A" = "(BE002A) Florennes", "EG002A" = "(EG002A) El Gorah", "FR001A" = "(FR001A) American Embassy Paris", "GM001A" = "(GM001A) Amberg", "GM002A" = "(GM002A) American Embassy Bad Godesberg", 
                                                             "GM003A" = "(GM003A) Armstrong Barracks Buedingen", "GM004A" = "(GM004A) Aschaffenburg", "GM005A" = "(GM005A) Babenbausen Kaserne", "GM006A" = "(GM006A) Bad Kissingen", "GM007A" = "(GM007A) Bad Kreuznach", 
                                                             "GM008A" = "(GM008A) Barton Barracks Ansbach", "GM009A" = "(GM009A) Berlin", "GM010A" = "(GM010A) Bindlach", "GM013A" = "(GM013A) Butzbach", "GM014A" = "(GM014A) Campbell Barracks Heidelberg", 
                                                             "GM015A" = "(GM015A) Carl-Schurz Bremerhaven", "GM016A" = "(GM016A) Conn Barracks Schweinfurt", "GM017A" = "(GM017A) Crailsheim", "GM018A" = "(GM018A) Darmstadt", 
                                                             "GM019A" = "(GM019A) Dexheim Military Community", "GM020A" = "(GM020A) Ferris Barracks Erlangen", "GM021A" = "(GM021A) Field Station Bad Aibling", "GM022A" = "(GM022A) Fischbach", 
                                                             "GM023A" = "(GM023A) Flensburg", "GM024A" = "(GM024A) Frankfurt", "GM025A" = "(GM025A) Friedberg", "GM026A" = "(GM026A) Fulda", "GM027A" = "(GM027A) Furth", "GM028A" = "(GM028A) Garlstadt", 
                                                             "GM029A" = "(GM029A) Garmisch", "GM030A" = "(GM030A) Geilenkirchen", "GM031A" = "(GM031A) Gelnhausen", "GM032A" = "(GM032A) Germersheim", "GM033A" = "(GM033A) Gerszewski Barracks Knielingen", 
                                                             "GM034A" = "(GM034A) Giebelstadt", "GM035A" = "(GM035A) Giessen", "GM036A" = "(GM036A) Goeppengen", "GM037A" = "(GM037A) Grafenwohr", "GM038A" = "(GM038A) H D Smith Barracks Baumholder", 
                                                             "GM040A" = "(GM040A) Hanau", "GM041A" = "(GM041A) Harvey Barracks Kitzingen", "GM042A" = "(GM042A) Heidelberg", "GM043A" = "(GM043A) Heilbronn", "GM044A" = "(GM044A) Herzogenaurauch", 
                                                             "GM045A" = "(GM045A) Hessisch-Oldendorf", "GM046A" = "(GM046A) Hindenburg Kaserne Ansbach", "GM047A" = "(GM047A) Hohenfels", "GM048A" = "(GM048A) Idar-Oberstein", 
                                                             "GM049A" = "(GM049A) Illesheim", "GM050A" = "(GM050A) Kaapaun Air Station", "GM051A" = "(GM051A) Kaefertal", "GM052A" = "(GM052A) Kaiserslautern", "GM054A" = "(GM054A) Karlsruhe", 
                                                             "GM055A" = "(GM055A) Katterbach Kaserne", "GM056A" = "(GM056A) Kelley Barracks Mohringen", "GM057A" = "(GM057A) Kirchgoens", "GM058A" = "(GM058A) Landstuhl Medical Center", 
                                                             "GM059A" = "(GM059A) Larson Barracks Kitzingen", "GM060A" = "(GM060A) Ledward Barracks Schweinfurt", "GM062A" = "(GM062A) Ludwigsburg", "GM063A" = "(GM063A) Main-Kastel", 
                                                             "GM064A" = "(GM064A) Mainz", "GM065A" = "(GM065A) Mannheim", "GM066A" = "(GM066A) McGraw Kaserne Augsburg", "GM067A" = "(GM067A) McPheeter Bad Hersfeld", "GM068A" = "(GM068A) Miesau Army Depot", 
                                                             "GM069A" = "(GM069A) Munich", "GM070A" = "(GM070A) Nellingen", "GM072A" = "(GM072A) New Ulm", "GM073A" = "(GM073A) Nurnburg", "GM074A" = "(GM074A) Oberursel", "GM075A" = "(GM075A) Panzer Kaserne Boblingen", 
                                                             "GM076A" = "(GM076A) Patch Barracks Vaihingen", "GM077A" = "(GM077A) Patton Barracks Heidelberg", "GM078A" = "(GM078A) Peden Barracks Wertheim", "GM079A" = "(GM079A) Pinder Barracks Zirndorf", 
                                                             "GM080A" = "(GM080A) Pirmasens", "GM081A" = "(GM081A) Pruem", "GM083A" = "(GM083A) Reese Barracks Augsburg", "GM085A" = "(GM085A) Rheinberg", "GM086A" = "(GM086A) Rhineland Kaserne Ettlingen", 
                                                             "GM087A" = "(GM087A) Rose Barracks Bad Kreuznach", "GM088A" = "(GM088A) Sandhofen", "GM089A" = "(GM089A) Schwabach", "GM090A" = "(GM090A) Schwabisch Hall", "GM091A" = "(GM091A) Schwaebisch Gmund", 
                                                             "GM092A" = "(GM092A) Schwetzingen", "GM093A" = "(GM093A) Seckenheim", "GM095A" = "(GM095A) Sheridan Kaserne Augsburg", "GM096A" = "(GM096A) Sorghof", "GM098A" = "(GM098A) Strub Kaserne Berchtesgaden", 
                                                             "GM099A" = "(GM099A) Stuttgart", "GM100A" = "(GM100A) Stuttgart Airport Echterdingen", "GM102A" = "(GM102A) Tompkin Barracks Schwetzingen", "GM103A" = "(GM103A) Viseck", 
                                                             "GM104A" = "(GM104A) Warner Barracks Bamberg", "GM105A" = "(GM105A) Wiesbaden", "GM107A" = "(GM107A) Wildflecken", "GM108A" = "(GM108A) Worms", "GM109A" = "(GM109A) Wuerzberg", 
                                                             "IT001A" = "(IT001A) American Embassy Rome", "IT004A" = "(IT004A) Camp Darby Livorno", "IT012A" = "(IT012A) Vicenza", "JA003A" = "(JA003A) Camp Zama Tokyo", "JA011A" = "(JA011A) Torii Station Okinawa", 
                                                             "KS001A" = "(KS001A) 19th Support Command Camp Henry Taegu", "KS003A" = "(KS003A) 23rd Area Support Group Camp Humphreys", "KS004A" = "(KS004A) 34th Area Support Group Pusan", 
                                                             "KS005A" = "(KS005A) Camp Carroll Waegwan", "KS006A" = "(KS006A) Camp Casey Tongduchon", "KS007A" = "(KS007A) Camp Long Wongju Kangwon-Bo", "KS008A" = "(KS008A) Camp Market Bupyeong", 
                                                             "KS009A" = "(KS009A) Camp Red Cloud Uijonbu", "KS015A" = "(KS015A) Seoul", "KS018A" = "(KS018A) Taejon", "KS019A" = "(KS019A) Yongsan", "KU001A" = "(KU001A) Combat Support Kuwait City", 
                                                             "NL001A" = "(NL001A) Brunssum", "PM002A" = "(PM002A) Army Garrison", "PM004A" = "(PM004A) Fort Kobbe", "PM005A" = "(PM005A) Fort William Davis", "SA002A" = "(SA002A) Dhahran", "SA005A" = "(SA005A) Riyadh", 
                                                             "TU006A" = "(TU006A) Sinop", "06073D" = "(06073D) Tracy Defense Depot Stockton", "08002D" = "(08002D) DFAS Center Denver", "11002D" = "(11002D) DFAS Center Washington", 
                                                             "11003D" = "(11003D) DFAS Headquarters Washington", "11006D" = "(11006D) Ntl Imagery and Mapping Agcy Hydro/Topographc Ctr Washingtn", "18002D" = "(18002D) DFAS Center Indianapolis", 
                                                             "20002D" = "(20002D) Defense Industrial Plant Equipment Facility Atchison", "29004D" = "(29004D) DFAS Center Kansas City", "35002D" = "(35002D) Defense Nuclear Agency Los Alamos", 
                                                             "36022D" = "(36022D) US Mission United Nations New York City", "39003D" = "(39003D) Columbus Defense Depot", "39004D" = "(39004D) Dayton Electronics Center", "39005D" = "(39005D) DFAS Center Cleveland", 
                                                             "39006D" = "(39006D) DFAS Center Columbus", "42004D" = "(42004D) Defense Depot Region East Northwest Cumberland", "42010D" = "(42010D) Philadelphia Industrial Center", 
                                                             "42013D" = "(42013D) Philadelphia Personnel Center", "47006D" = "(47006D) Memphis Defense Depot", "49004D" = "(49004D) Ogden Defense Depot", "51003D" = "(51003D) Cameron Station Alexandria", 
                                                             "51022D" = "(51022D) Department of Defense Activities Pentagon", "51026D" = "(51026D) Richmond Defense Depot", "04008001" = "(04008001) BUCKLEY AGB", "04008002" = "(04008002) PETERSON AFB", "04008003" = "(04008003) SCHRIEVER AFB", 
                                                             "04008004" = "(04008004) LAMAR COMMFAC ANNEX", "04008005" = "(04008005) LOWRY AFB", "04008009" = "(04008009) USAF ACADEMY", "04009001" = "(04009001) STRATFORD ADM", "04009002" = "(04009002) BRADLEY IAP-AGS", 
                                                             "04009003" = "(04009003) ORANGE AGS", "04010001" = "(04010001) DOVER AFB", "04011001" = "(04011001) BOLLING AFB", "04012001" = "(04012001) PATRICK AFB", "04012004" = "(04012004) EGLIN AFB", "04012005" = "(04012005) HURLBURT FIELD", 
                                                             "04012008" = "(04012008) HOMESTEAD AFB", "04012010" = "(04012010) JACKSONVILLE AFS", "04012012" = "(04012012) MACDILL AFB", "04012014" = "(04012014) RICHMOND AFS", "04012015" = "(04012015) TYNDALL AFB", "04013004" = "(04013004) DOBBINS ARB", 
                                                             "04013005" = "(04013005) MCCOLLUM AGS", "04013007" = "(04013007) MOODY AFB", "04013008" = "(04013008) ROBINS AFB", "04013010" = "(04013010) SAVANNAH AFS", "04013011" = "(04013011) SPENCE AUX AFLD (CLOSED)", 
                                                             "04013012" = "(04013012) STATESBORO BOMB SCORING SITE", "04015001" = "(04015001) HICKAM AFB", "04016001" = "(04016001) BOISE AIR TERM AGS", "04016002" = "(04016002) MOUNTAIN HOME AFB", "04017001" = "(04017001) SCOTT AFB", 
                                                             "04017002" = "(04017002) CHANUTE AFB", "04017003" = "(04017003) OHARE IAP ARS", "04018001" = "(04018001) FORT WAYNE MAP AGS", "04018002" = "(04018002) GRISSOM AFB", "04018003" = "(04018003) HULMAN REG ARPT-AGS", 
                                                             "04019001" = "(04019001) DES MOINES IAP-AGS", "04019002" = "(04019002) FORT DODGE", "04019004" = "(04019004) SIOUX CITY MAP AGS", "04020001" = "(04020001) MCCONNELL AFB", "04020002" = "(04020002) FORBES FIELD AGS", 
                                                             "04021001" = "(04021001) STANDIFORD FIELD AGS", "04022001" = "(04022001) BARKSDALE AFB", "04022002" = "(04022002) CLAIBORNE WPNS RANGE 01", "04022003" = "(04022003) ENGLAND AFB", "04022004" = "(04022004) HAMMOND AGS", 
                                                             "04022007" = "(04022007) SLIDELL RADAR SITE", "04023001" = "(04023001) LORING AFB", "04023002" = "(04023002) BANGOR ANG", "04023007" = "(04023007) S. PORTLAND AGS", "04024003" = "(04024003) ANDREWS AFB", 
                                                             "04025002" = "(04025002) AF PLANT 28", "04025005" = "(04025005) BARNES MAP AGS", "04025006" = "(04025006) CAPE COD AFS", "04025007" = "(04025007) HANSCOM AFB", "04025009" = "(04025009) N. TRURO AFS", 
                                                             "04025010" = "(04025010) OTIS AGB", "04025014" = "(04025014) WELLESLEY AGS", "04025015" = "(04025015) WESTOVER ARB AFB", "04026001" = "(04026001) BAYSHORE BOMB SCORING SITE", "04026002" = "(04026002) K.I.SAWYER AFB", 
                                                             "04026003" = "(04026003) W.K.KELLOGG REG ARPT AGS", "04026005" = "(04026005) PORT AUSTIN AFS", "04026008" = "(04026008) WURTSMITH AFB", "04026009" = "(04026009) SELFRIDGE ANG BASE", "04027001" = "(04027001) BAUDETTE AFS (CLOSED)", 
                                                             "04027002" = "(04027002) DULUTH AGS", "04027004" = "(04027004) FINLAND AFS (CLOSED)", "04027005" = "(04027005) MINN/ST PAUL IAP ARS", "04028001" = "(04028001) COLUMBUS AFB", "04028003" = "(04028003) ALLEN C THOMPSON FIELD-AGS", 
                                                             "04028004" = "(04028004) KEESLER AFB", "04028006" = "(04028006) KEY FIELD AGS", "04029001" = "(04029001) ST LOUIS AFS", "04029002" = "(04029002) AF PLANT 65", "04029003" = "(04029003) AF PLANT 84", 
                                                             "04029005" = "(04029005) JEFFERSON BARRACKS AGS", "04029006" = "(04029006) LAMBERT ST LOUIS IAP AGS", "04029007" = "(04029007) RICHARDS-GEBAUR ARS", "04029008" = "(04029008) ROSECRANS MEM ARPT-AGS", "04029009" = "(04029009) WHITEMAN AFB", 
                                                             "04030001" = "(04030001) OPHEIM AFS (CLOSED)", "04030002" = "(04030002) MALMSTROM AFB", "04030004" = "(04030004) KALISPELL AFS (CLOSED)", "04031002" = "(04031002) LINCOLN MAP AGS", "04031003" = "(04031003) OFFUTT AFB", 
                                                             "04032004" = "(04032004) NELLIS AFB", "04032005" = "(04032005) HAWTHORNE BOMB SCORING SITE", "04033002" = "(04033002) PEASE AFB/AGB", "04033003" = "(04033003) NEW BOSTON AFS", "04033004" = "(04033004) PEASE AGB", 
                                                             "04034001" = "(04034001) TETERBORO MAP", "04034003" = "(04034003) GIBBSBORO AFS", "04034004" = "(04034004) MCGUIRE AFB", "04035003" = "(04035003) CANNON AFB", "04035004" = "(04035004) HOLLOMAN AFB", "04035006" = "(04035006) KIRTLAND AFB", 
                                                             "04036001" = "(04036001) FISHERS ISLAND", "04036002" = "(04036002) AF PLANT 38", "04036004" = "(04036004) AF PLANT 59", "04036008" = "(04036008) GRIFFISS NOAD ANG", "04036009" = "(04036009) NIAGARA FALLS IAP-ARS", 
                                                             "04036011" = "(04036011) HANCOCK FIELD AGS", "04036012" = "(04036012) LOCKPORT AFS", "04036013" = "(04036013) MONTAUK", "04036015" = "(04036015) PLATTSBURGH AFB", "04036017" = "(04036017) ROSLYN AGS", 
                                                             "04036019" = "(04036019) SCHENECTADY ARPT-AGS", "04036022" = "(04036022) SUFFOLK CTY ARPT-AGS", "04036023" = "(04036023) TUMMONDS HILL TEST ANNEX", "04037001" = "(04037001) BADIN AGS", "04037002" = "(04037002) CHARLOTTE/DOUGLAS IAP AGS", 
                                                             "04037003" = "(04037003) FORT FISHER AFS", "04037004" = "(04037004) DARE COUNTY WPNS RANGE", "04037005" = "(04037005) POPE AFB", "04037006" = "(04037006) SEYMOUR JOHNSON AFB", "04037007" = "(04037007) WADESBORO AGS", 
                                                             "04038002" = "(04038002) GRAND FORKS AFB", "04038004" = "(04038004) FORTUNA AFS (CLOSED)", "04038006" = "(04038006) FARGO/HECTOR FIELD", "04038007" = "(04038007) MINOT AFB", "04039001" = "(04039001) AF PLANT 27", 
                                                             "04039003" = "(04039003) AF PLANT 47", "04039008" = "(04039008) RICKENBACKER AGB", "04039009" = "(04039009) MANSFIELD LAHM AIRPORT ANG", "04039011" = "(04039011) SP FLD-BECKLEY MAP AGS", "04039012" = "(04039012) TOLEDO EXPRESS ARPT-AGS", 
                                                             "04039013" = "(04039013) WRIGHT-PATTERSON AFB", "04039014" = "(04039014) YOUNGSTOWN MAP ARS", "04039015" = "(04039015) ZANESVILLE AGS", "04039016" = "(04039016) NEWARK AFS", "04040001" = "(04040001) TULSA INTERNATIONAL AIRPORT", 
                                                             "04040002" = "(04040002) ALTUS AFB", "04040006" = "(04040006) TINKER AFB", "04040008" = "(04040008) VANCE AFB", "04041003" = "(04041003) MOUNT HEBO AFS (CLOSED)", "04041005" = "(04041005) PORTLAND IAP AGS", 
                                                             "04042002" = "(04042002) GR. PITTS IAP-AGS", "04042003" = "(04042003) HARRISBURG OLMSTED IAP-AGS", "04042005" = "(04042005) STATE COLLEGE ANG STA", "04042007" = "(04042007) WYOMING VALLEY ANG CTR", "04044001" = "(04044001) PROVIDENCE PRT", 
                                                             "04044002" = "(04044002) ARMORY OF MOUNTED COMMANDS", "04044003" = "(04044003) CRANSTON STREET ARMORY", "04044004" = "(04044004) COVENTRY AGS", "04044005" = "(04044005) N. SMITHFIELD AGS", "04044006" = "(04044006) QUONSET STATE AIRPORT AGS", 
                                                             "04044007" = "(04044007) THEODORE F. GREEN MAP", "04045002" = "(04045002) CHARLESTON AFB", "04045004" = "(04045004) MYRTLE BEACH AFB", "04045006" = "(04045006) SHAW AFB", "04046001" = "(04046001) ELLSWORTH AFB", 
                                                             "04046002" = "(04046002) SIOUX FALLS CTR", "04047001" = "(04047001) ALCOA AGS", "04047002" = "(04047002) ARNOLD AFB", "04047003" = "(04047003) NASHVILLE METRO ARPT-AGS", "04047004" = "(04047004) LOVELL FIELD", 
                                                             "04047005" = "(04047005) MCGHEE TYSON ARPT-AGS", "04047006" = "(04047006) MEMPHIS IAP AGS", "04048002" = "(04048002) AF PLANT 04", "04048004" = "(04048004) BERGSTROM AFB", "04048005" = "(04048005) BROOKS AFB", 
                                                             "04048006" = "(04048006) CARSWELL AFB", "04048007" = "(04048007) BERGSTROM ARB", "04048009" = "(04048009) DYESS AFB", "04048011" = "(04048011) LYNDON B. JOHNSON SPACE CTR", "04048012" = "(04048012) GARLAND AGS", 
                                                             "04048013" = "(04048013) GOODFELLOW AFB", "04048015" = "(04048015) KELLY AFB", "04048016" = "(04048016) LA PORTE AGS", "04048017" = "(04048017) LACKLAND AFB", "04048018" = "(04048018) LAUGHLIN AFB", "04048019" = "(04048019) NEDERLAND AGS", 
                                                             "04048020" = "(04048020) ODESSA RADAR SITE", "04048021" = "(04048021) RANDOLPH AFB", "04048022" = "(04048022) REESE AFB", "04048026" = "(04048026) SHEPPARD AFB", "04048027" = "(04048027) WEBB AFB (CLOSED)", "04049001" = "(04049001) HILL AFB", 
                                                             "04049002" = "(04049002) AF PLANT 78", "04049005" = "(04049005) SALT LAKE CITY IAP AGS", "04050001" = "(04050001) BURLINGTON IAP-AGS", "04051001" = "(04051001) RICHMOND IAP AGS", "04051002" = "(04051002) ALEXANDRIA", 
                                                             "04051003" = "(04051003) LANGLEY AFB", "04051004" = "(04051004) PENTAGON - AIR FORCE", "04053001" = "(04053001) BELLINGHAM MAP", "04053002" = "(04053002) FAIRCHILD AFB", "04053005" = "(04053005) MCCHORD AFB", "04053007" = "(04053007) PAINE AGS", 
                                                             "04053008" = "(04053008) SEATTLE AGB", "04053009" = "(04053009) SPOKANE IAP AGS", "04054001" = "(04054001) YEAGER ARPT AGS", "04054002" = "(04054002) SHEPHERD FLD AGS (EWRVA)", "04055001" = "(04055001) GEN BILLY MITCHELL FIELD/RSV CTR", 
                                                             "04055002" = "(04055002) TRUAX FIELD ANG STA", "04055003" = "(04055003) VOLK FIELD ANG BASE", "04056001" = "(04056001) BOULDER RESEARCH SITE", "04056004" = "(04056004) FRANCIS E WARREN AFB", 
                                                             "05006001" = "(05006001) DEF DISTRIBUTION CTR-SAN JOAQUIN", "05011002" = "(05011002) DMA HYDRO/TOPOGRAPHIC CTR", "05015001" = "(05015001) KUMA DEF COMM CTR", "05020001" = "(05020001) DEF INDUST PLANT EQUIP FAC", 
                                                             "05026001" = "(05026001) BATTLE CREEK FEDERAL CENTER", "05029001" = "(05029001) ST LOUIS FEDERAL CENTER", "05035001" = "(05035001) DEF NUCLEAR AGCY", "05036001" = "(05036001) US MISSIONS-UNITED NATIONS", 
                                                             "05039001" = "(05039001) COLUMBUS DEF DEPOT", "05039005" = "(05039005) ELECTRONICS CTR - DAYTON", "05042001" = "(05042001) PERSONNEL CTR - PHILA", "05042002" = "(05042002) DEFENSE SUPPLY CTR PHILA", 
                                                             "05042006" = "(05042006) DEFENSE DIST DEPOT SUSQUEHANNA", "05047001" = "(05047001) MEMPHIS DEF DEPOT", "05049001" = "(05049001) DEF DIST DEPOT OGDEN UTAH", "05051001" = "(05051001) PENTAGON - DOD", "05051002" = "(05051002) RICHMOND DEF DEPOT", 
                                                             "05051003" = "(05051003) CAMERON STATION", "05051004" = "(05051004) DISA HQTRS", "06008005" = "(06008005) DFAS DENVER CENTER", "06011001" = "(06011001) DFAS WASHINGTON CENTER", "06011002" = "(06011002) DFAS HEADQUARTERS", 
                                                             "06018001" = "(06018001) DFAS INDIANAPOLIS CENTER", "06029001" = "(06029001) DFAS KANSAS CITY CENTER", "06039001" = "(06039001) DFAS COLUMBUS CENTER", "06039002" = "(06039002) DFAS CLEVELAND CENTER", "07012001" = "(07012001) SOUTHERN COMMAND", 
                                                             "08001001" = "(08001001) USCG DAUPHINE ISLAND", "08002001" = "(08002001) USCG ANCHORAGE", "08002002" = "(08002002) USCG KODIAK", "08002003" = "(08002003) USCG JUNEAU", "08002004" = "(08002004) USCG SITKA", 
                                                             "08002005" = "(08002005) USCG KETCHIKAN", "08002006" = "(08002006) USCG VALDEZ", "08006001" = "(08006001) SAN PEDRO COAST GUARD", "08006002" = "(08006002) USCG TRACEN PETALUMA", "08009001" = "(08009001) COAST GUARD ACADEMY", 
                                                             "08012001" = "(08012001) KEY WEST COAST GUARD", "08012002" = "(08012002) MIAMI COAST GUARD", "08015001" = "(08015001) SAND ISLAND COAST GUARD", "08024001" = "(08024001) CURTIS BAY COAST GUARD", "08029001" = "(08029001) ST LOUIS COAST GUARD", 
                                                             "08031001" = "(08031001) USCG ELIZABETH CITY NC", "08036001" = "(08036001) USCG NIAGARA NY", "08048001" = "(08048001) GALVESTON COAST GUARD", "08048002" = "(08048002) CORPUS CHRISTI COAST GUARD", "08051001" = "(08051001) USCG HAMPTON ROADS VA", 
                                                             "08051002" = "(08051002) USCG ALEXANDRIA VA", "08051003" = "(08051003) USCG YORKTOWN VA", "08051004" = "(08051004) USCG CAPE CHARLES VA", "01001000" = "(01001000) ALLEN FIELD", "01001001" = "(01001001) BIRMINGHAM SUPPORT", 
                                                             "01001002" = "(01001002) ALABAMA ARMY AMMO PLANT", "01001003" = "(01001003) ANNISTON ARMY DEPOT", "01001004" = "(01001004) FT GEORGE WALLACE MONTGOMERY", "01001005" = "(01001005) ENDIST MOBILE AL", "01001006" = "(01001006) DOTHAN AG", 
                                                             "01001007" = "(01001007) WRIGHT USARC MOBILE", "01001008" = "(01001008) FORT MCCLELLAN", "01001009" = "(01001009) HAMILTON", "01001010" = "(01001010) REDSTONE ARSENAL", "01001011" = "(01001011) FORT RUCKER", 
                                                             "01002000" = "(01002000) BLACK RAPIDS TNG SITE", "01002002" = "(01002002) FORT RICHARDSON", "01002003" = "(01002003) FORT JONATHAN WAINWRIGHT", "01002004" = "(01002004) ENDIST ALASKA ANCHORAGE", "01004002" = "(01004002) FORT HUACHUCA", 
                                                             "01004003" = "(01004003) PHOENIX ARNG", "01004004" = "(01004004) YUMA PROVING GROUND", "01004005" = "(01004005) NAVAJO ARMY DEPOT ACT", "01005001" = "(01005001) MTA CAMP ROBINSON", "01005002" = "(01005002) ENDIST LITTLE ROCK AR", 
                                                             "01005003" = "(01005003) PINE BLUFF ARSENAL", "01006001" = "(01006001) HAMILTON FIELD", "01006003" = "(01006003) SIERRA ARMY DEPOT", "01006005" = "(01006005) FORT IRWIN", "01006006" = "(01006006) FORT MACARTHUR", 
                                                             "01006008" = "(01006008) LOS ALAMITOS AFRC", "01006009" = "(01006009) OAKLAND USAR CENTER", "01006010" = "(01006010) PRESIDIO OF MONTEREY", "01006011" = "(01006011) CAMP ROBERTS", "01006012" = "(01006012) RIVERBANK ARMY AMMO PLANT", 
                                                             "01006013" = "(01006013) FORT ORD/DOD CENTER", "01006014" = "(01006014) SACRAMENTO ARMY DEPOT", "01006015" = "(01006015) PRESIDIO OF SAN FRANCISCO", "01006016" = "(01006016) SHARPE ARMY DEPOT", "01006017" = "(01006017) ENDIST LOS ANGELES CA", 
                                                             "01006018" = "(01006018) ENDIST SAN FRANCISCO CA", "01006019" = "(01006019) ENDIST SACRAMENTO CA", "01006020" = "(01006020) CAMP PARKS", "01008001" = "(01008001) FORT COLLINS", "01008002" = "(01008002) FORT CARSON", 
                                                             "01008003" = "(01008003) FITZSIMONS ARMY MED CTR", "01008005" = "(01008005) ROCKY MTN ARSENAL", "01008006" = "(01008006) PUEBLO ARMY DEPOT ACT", "01009001" = "(01009001) FORT NATHAN HALE", "01009002" = "(01009002) STRATFORD ARMY ENGINE PLANT", 
                                                             "01011001" = "(01011001) FORT LESLIE J MCNAIR", "01011002" = "(01011002) WALTER REED ARMY MED CTR", "01011003" = "(01011003) ARMY ATTACHE DEPT OF STATE", "01012001" = "(01012001) FORT MYERS", "01012002" = "(01012002) CAMP BLANDING", 
                                                             "01012003" = "(01012003) HQ STRICOM ORLANDO", "01012004" = "(01012004) JACKSONVILLE ENDIST", "01013001" = "(01013001) FORT VALLEY", "01013003" = "(01013003) FORT BENNING", "01013004" = "(01013004) FORT GORDON", 
                                                             "01013006" = "(01013006) FORT GILLEM", "01013007" = "(01013007) FORT STEWART", "01013008" = "(01013008) FORT MCPHERSON", "01013009" = "(01013009) ENDIST SAVANNAH GEORGIA", "01015013" = "(01015013) FORT SHAFTER", 
                                                             "01015014" = "(01015014) SCHOFIELD BARRACKS", "01015015" = "(01015015) TRIPLER ARMY MEDICAL CENTER", "01016001" = "(01016001) GOWEN FIELD", "01017001" = "(01017001) CHARLES MELVIN PRICE CTR", "01017002" = "(01017002) JOLIET AAP/AFRC", 
                                                             "01017003" = "(01017003) ROCK ISLAND ARSENAL", "01017005" = "(01017005) FORT SHERIDAN", "01017006" = "(01017006) SAVANNA ARMY DEPOT ACT", "01018001" = "(01018001) FORT BENJAMIN HARRISON", "01018004" = "(01018004) INDIANA ARMY AMMO PLANT", 
                                                             "01018005" = "(01018005) JEFFERSON PROVING GROUND", "01018006" = "(01018006) NEWPORT ARMY AMMO PLANT", "01019002" = "(01019002) FORT DES MOINES", "01019003" = "(01019003) IOWA ARMY AMMO PLANT", "01020002" = "(01020002) KANSAS ARMY AMMO PLAN", 
                                                             "01020003" = "(01020003) FORT LEAVENWORTH", "01020004" = "(01020004) FORT RILEY", "01020005" = "(01020005) SUNFLOWER ARMY AMMO PLANT", "01021001" = "(01021001) LEXINGTON BLUE GRASS DEPOT", "01021002" = "(01021002) FORT CAMPBELL", 
                                                             "01021003" = "(01021003) FORT KNOX", "01021004" = "(01021004) ENDIST LOUISVILLE KY", "01021005" = "(01021005) LOUISVILLE ARMY RES KY", "01022001" = "(01022001) NEW ORLEANS MIL OC. TERMINAL", "01022003" = "(01022003) FORT POLK", 
                                                             "01022004" = "(01022004) NEW ORLEANS ENDIST", "01023001" = "(01023001) AUGUSTA ARMORY GUARD", "01024001" = "(01024001) ADELPHI LAB CENTER", "01024002" = "(01024002) ABERDEEN PROVING GROUND", "01024004" = "(01024004) FORT DETRICK", 
                                                             "01024005" = "(01024005) USARC CUMBERLAND", "01024006" = "(01024006) FORT GEORGE G. MEADE", "01024007" = "(01024007) FORT RITCHIE", "01024008" = "(01024008) BALTIMORE ENDIST/CIV PERSONNEL CTR", "01025002" = "(01025002) FORT DEVENS", 
                                                             "01025003" = "(01025003) CAMP EDWARDS - NG", "01025004" = "(01025004) USA NATICK RSCH & DEV CTR", "01025005" = "(01025005) S. BOSTON USARC", "01025006" = "(01025006) USA MAT & TECH CTR WATERTOWN", 
                                                             "01025007" = "(01025007) ENDIST NEW ENGLAND CONCORD", "01026001" = "(01026001) FORT CUSTER TRNG CTR", "01026002" = "(01026002) DETROIT ARSENAL", "01026003" = "(01026003) ENDIST DETROIT", "01026005" = "(01026005) MICHIGAN ARMY MISSILE PLANT", 
                                                             "01027001" = "(01027001) CAMP RIPLEY", "01027002" = "(01027002) TWIN CITIES ARMY AMMO PLANT", "01027003" = "(01027003) FORT SNELLING", "01028001" = "(01028001) MISSISSIPPI ARMY AMMO PLANT", "01028002" = "(01028002) CAMP MCCAIN-NG", 
                                                             "01028003" = "(01028003) CAMP SHELBY", "01028004" = "(01028004) VICKSBURG ENDIST", "01029001" = "(01029001) LAKE CITY ARMY AMMO PLANT", "01029002" = "(01029002) GATEWAY ARMY AMMO PLANT", "01029003" = "(01029003) ST LOUIS ARMY RESERVE", 
                                                             "01029004" = "(01029004) FORT LEONARD WOOD", "01029005" = "(01029005) ST LOUIS ENDIST", "01029006" = "(01029006) KANSAS CITY ENDIST", "01030001" = "(01030001) FORT MISSOULA USARC", "01030002" = "(01030002) FORT WILLIAM H. HARRISON", 
                                                             "01031001" = "(01031001) CORNHUSKER ARMY AMMO PLANT", "01031002" = "(01031002) MEAD FAC NG", "01031003" = "(01031003) ENDIST OMAHA NE", "01032000" = "(01032000) LAKE MEAD BASE LAS VEGAS", "01032001" = "(01032001) HAWTHORNE ARMY AMMO PLANT", 
                                                             "01033001" = "(01033001) ARMY COLD REGIONS RSCH LAB", "01033002" = "(01033002) STATE MIL. RESERVATION", "01034001" = "(01034001) FORT DIX", "01034002" = "(01034002) FORT HAMILTON", "01034003" = "(01034003) FORT MONMOUTH", 
                                                             "01034007" = "(01034007) PICATINNY ARSENAL", "01035001" = "(01035001) WHITE SANDS MISSILE RANGE", "01035002" = "(01035002) FORT WINGATE DEPOT ACT", "01035003" = "(01035003) ENDIST ALBUQUERQUE NM", 
                                                             "01036001" = "(01036001) PFC ROBERT J. MANVILLE USARC", "01036002" = "(01036002) FORT DRUM", "01036003" = "(01036003) GALEVILLE TRNG SITE", "01036004" = "(01036004) ENDIST BUFFALO NY", "01036005" = "(01036005) SENECA ARMY DEPOT", 
                                                             "01036006" = "(01036006) LATHAM COMPLEX (ST HQS)", "01036007" = "(01036007) ENDIST NEW YORK NY", "01036008" = "(01036008) WATERVLIET ARSENAL", "01036009" = "(01036009) WEST POINT MILRES", "01036010" = "(01036010) STEWART NEWBURGH USARC", 
                                                             "01037001" = "(01037001) USARC OAK RIDGE", "01037002" = "(01037002) FORT BRAGG", "01037003" = "(01037003) SUNNYPOINT MIL OCEAN TERM", "01037004" = "(01037004) TARHEEL ARMY MISSILE PLANT", "01039001" = "(01039001) LIMA ARMY TANK CTR", 
                                                             "01039002" = "(01039002) PORT CLINTON IND PARK", "01039003" = "(01039003) RAVENNA ARMY AMMO PLANT", "01039004" = "(01039004) BROOKLYN USARC", "01039005" = "(01039005) COLUMBUS-BEIGHTLER (TAG)", "01040001" = "(01040001) MCALESTER ARMY AMMO PLANT", 
                                                             "01040002" = "(01040002) ENDIST TULSA OK", "01040003" = "(01040003) FORT SILL", "01041001" = "(01041001) UMATILLA DEPOT", "01041002" = "(01041002) SALEM ARMORY", "01042002" = "(01042002) CARLISLE BARRACKS", 
                                                             "01042003" = "(01042003) LETTERKENNY ARMY DEPOT", "01042004" = "(01042004) PITTSBURGH MEPS / ENDIST", "01042006" = "(01042006) USARC FT INDIANTOWN GAP", "01042007" = "(01042007) SCRANTON ARMY AMMO PLANT", 
                                                             "01042008" = "(01042008) CHARLES KELLY SPT FACILITY", "01042009" = "(01042009) TOBYHANNA ARMY DEPOT", "01044001" = "(01044001) NORTH SCITUATE ANG ORG MAINT4", "01044002" = "(01044002) NG/RSV WARWICK", "01045001" = "(01045001) FORT JACKSON", 
                                                             "01047001" = "(01047001) HOLSTON ARMY AMMO PLANT", "01047002" = "(01047002) MILAN ARMY AMMO PLANT", "01047003" = "(01047003) VOLUNTEER ARMY AMMO PLANT", "01048001" = "(01048001) FORT WORTH USARC", "01048002" = "(01048002) ENDIST FORT WORTH TX", 
                                                             "01048003" = "(01048003) FORT BLISS", "01048004" = "(01048004) ENDIST GALVESTON TX", "01048007" = "(01048007) FORT HOOD", "01048008" = "(01048008) FORT SAM HOUSTON", "01048009" = "(01048009) SAN ANTONIO CALLAGHAN USAREC", 
                                                             "01048010" = "(01048010) LONGHORN ARMY AMMO PLANT", "01048011" = "(01048011) RED RIVER DEPOT", "01048012" = "(01048012) CAMP SWIFT", "01048013" = "(01048013) CORPUS CHRISTI ARMY DEPOT", "01049000" = "(01049000) GREEN RIVER TEST COMPLEX", 
                                                             "01049003" = "(01049003) CAMP W G WILLIAMS", "01049004" = "(01049004) DUGWAY PROVING GROUND", "01049005" = "(01049005) TOOELE ARMY DEPOT", "01049006" = "(01049006) DESERET CHEMICAL DEPOT", "01050001" = "(01050001) ETHAN ALLEN FACILITY", 
                                                             "01050002" = "(01050002) TS CAMP JOHNSON GUARD", "01051001" = "(01051001) PENTAGON - ARMY", "01051003" = "(01051003) FORT BELVOIR", "01051004" = "(01051004) NORFOLK ENDIST", "01051005" = "(01051005) FORT A.P. HILL", 
                                                             "01051006" = "(01051006) FORT EUSTIS", "01051007" = "(01051007) FORT STORY", "01051008" = "(01051008) FORT LEE", "01051009" = "(01051009) FORT MONROE", "01051010" = "(01051010) FORT MYER", "01051012" = "(01051012) RADFORD ARMY AMMO PLANT", 
                                                             "01051014" = "(01051014) VINT HILL FARMS STA", "01053001" = "(01053001) ENDIST SEATTLE WA", "01053002" = "(01053002) FORT LAWTON", "01053003" = "(01053003) FORT LEWIS", "01053004" = "(01053004) VANCOUVER BARRACKS", 
                                                             "01053005" = "(01053005) ENDIST WALLA WALLA WA", "01055001" = "(01055001) CAMP DOUGLAS", "01055002" = "(01055002) BADGER ARMY AMMO PLANT", "01055003" = "(01055003) FORT MCCOY", "01056001" = "(01056001) CAMP GUERNSEY", 
                                                             "02001001" = "(02001001) MOBILE NAVSTA", "02001002" = "(02001002) NAVMARCORESCEN MOBILE", "02002001" = "(02002001) ADAK NAS", "02006001" = "(02006001) MARE ISLAND NAV SHIPYD", "02006002" = "(02006002) NAVAL HOSPITAL LONG BEACH", 
                                                             "02006003" = "(02006003) ALAMEDA NAS", "02006004" = "(02006004) SAN DIEGO NAVSTA", "02006005" = "(02006005) SAN DIEGO NSC", "02006006" = "(02006006) NORTH ISLAND NAS", "02006007" = "(02006007) SAN DIEGO NTC", 
                                                             "02006009" = "(02006009) NAVAL MEDICAL CTR SAN DIEGO", "02006010" = "(02006010) SAN DIEGO NAVSUBBASE", "02006011" = "(02006011) CORONADO NAV AMPHIB BASE", "02006012" = "(02006012) MOFFETT FIELD NAS/ANG", 
                                                             "02006013" = "(02006013) STOCKTON NAVCOMMSTA", "02006014" = "(02006014) CENTERVILLE BEACH NAVFAC", "02006015" = "(02006015) POINT SUR NAVFAC", "02006016" = "(02006016) TREASURE ISLAND NAVSTA", "02006017" = "(02006017) CONCORD NAVWEAPSTA", 
                                                             "02006018" = "(02006018) EL CENTRO NAF", "02006019" = "(02006019) CROWS LANDING NAV AUX LDG FLD", "02006020" = "(02006020) NAVAL STATION LONG BEACH", "02006021" = "(02006021) SEAL BEACH NAVWEAPSTA", 
                                                             "02006022" = "(02006022) CHINA LAKE NAVWEAPCEN", "02006023" = "(02006023) NAVAL HOSPITAL OAKLAND", "02006024" = "(02006024) OAKLAND NSC", "02006025" = "(02006025) NAVAL POSTGRADUATE SCH", "02006026" = "(02006026) PORT HUENEME NCBC", 
                                                             "02006027" = "(02006027) LEMOORE NAS", "02006028" = "(02006028) PT MUGU NAS", "02006029" = "(02006029) FLEET ASW TRNG CTR PACIFIC", "02006030" = "(02006030) FLT CMBT TRNG CTR PACIFIC", "02006031" = "(02006031) NORTH ISLAND NV AVIATION DEPOT", 
                                                             "02009001" = "(02009001) NEW LONDON NAVSUBBASE", "02009004" = "(02009004) NAV WPNS INDUS RSV PLANT", "02010001" = "(02010001) LEWES NAVFAC", "02011002" = "(02011002) WASHINGTON NAVDIST HQ", "02011003" = "(02011003) NAVAL AIR FACILITY WASH DC", 
                                                             "02012000" = "(02012000) NAVAL WEAPONS IND RESERVE PLT", "02012001" = "(02012001) NAVAL TRAINING CTR ORLANDO", "02012002" = "(02012002) PENSACOLA NAS", "02012003" = "(02012003) CORRY STATION NTTC", "02012004" = "(02012004) JACKSONVILLE NAS", 
                                                             "02012005" = "(02012005) KEY WEST NAS", "02012006" = "(02012006) NAVAL HOSPITAL PENSACOLA", "02012007" = "(02012007) NAV ED & TRN PGM MGMT SPT ACT", "02012008" = "(02012008) JACKSONVILLE NAV AVIATION DEPOT", 
                                                             "02012010" = "(02012010) CECIL FIELD NAS", "02012011" = "(02012011) MAYPORT NAVSTA", "02012012" = "(02012012) WHITING FIELD NAS", "02012013" = "(02012013) NAV COASTAL SYSTEMS CTR", "02013001" = "(02013001) NAVY RECRUITING AREA THREE", 
                                                             "02013002" = "(02013002) ATLANTA NAS", "02013003" = "(02013003) KINGS BAY NAVSUBBASE", "02013004" = "(02013004) NV SUPPLY CORPS SCHOOL", "02015001" = "(02015001) NAVCAMS E. PACIFIC", "02015002" = "(02015002) BARBERS POINT NAS", 
                                                             "02015004" = "(02015004) PEARL HARBOR NAVAL SHIPYARD", "02015005" = "(02015005) NAVAL BASE PEARL HARBOR", "02016001" = "(02016001) NUC PWR TRNG UNIT IDAHO FALLS", "02017001" = "(02017001) NAVAL STATION GREAT LAKES", 
                                                             "02017002" = "(02017002) NAVAL HOSPITAL GREAT LAKES", "02017003" = "(02017003) GLENVIEW NAS", "02018001" = "(02018001) NAVAL IND RESERVE ORDNANCE PL", "02018002" = "(02018002) NAV AVIONICS CTR INDIANAPOLIS", 
                                                             "02018003" = "(02018003) CRANE NAVWEAPSUPPCEN", "02021001" = "(02021001) LOUISVILLE NWC", "02022001" = "(02022001) NEW ORLEANS NAS JRB", "02022002" = "(02022002) NEW ORLEANS NSA", "02023001" = "(02023001) WINTER HARBOR NAVSECGRUACT", 
                                                             "02023002" = "(02023002) BRUNSWICK NAS", "02023003" = "(02023003) CUTLER NAV COMM UNIT", "02023004" = "(02023004) NAV INDUSTRIAL RSV PLANT", "02024001" = "(02024001) NESEC ST. INGOES", "02024002" = "(02024002) ANNAPOLIS NS(INCL USNA)", 
                                                             "02024004" = "(02024004) NNMC BETHESDA", "02024005" = "(02024005) INDIAN HEAD NAV ORD STA", "02024006" = "(02024006) PATUXENT RIVER NAS", "02024007" = "(02024007) WHITE OAK NSWC DAHLGREN", "02025000" = "(02025000) DOD FAMILY HOUSING CHICOPEE", 
                                                             "02025001" = "(02025001) SOUTH WEYMOUTH NAS", "02025002" = "(02025002) NAVMAR RESCEN WORCHESTER MA", "02025003" = "(02025003) NAVPRO STRAT SYS PITTSFIELD", "02025004" = "(02025004) NAV WPNS INDUS RSV PLANT", 
                                                             "02026001" = "(02026001) NAVAL AIR FACILITY DETROIT", "02027000" = "(02027000) NAV PLANT REP OFF MINNEAPOLIS", "02027001" = "(02027001) NAVY ASTRONAUTICS GROUP", "02028001" = "(02028001) PASCAGOULA NAVSTA", 
                                                             "02028003" = "(02028003) GULFPORT NCBC", "02028004" = "(02028004) MERIDIAN NAS", "02029001" = "(02029001) NAVRESCEN ST LOUIS MO", "02032001" = "(02032001) FALLON NAS", "02033001" = "(02033001) PORTSMOUTH NAV SHIPYD", 
                                                             "02034000" = "(02034000) NAV AUD SVC NE REG CAMDEN NJ", "02034001" = "(02034001) EARLE NAVWEAPSTA", "02034002" = "(02034002) LAKEHURST NAV AIR ENGR CTR", "02036000" = "(02036000) NAV PLANT REP OFF DET BETHPAG", 
                                                             "02036001" = "(02036001) SCOTIA NAVAL ADM BALLSTON", "02036002" = "(02036002) NAVAL STATION BROOKLYN NY", "02036003" = "(02036003) NAVAL STATION STATEN ISLAND", "02037000" = "(02037000) HARVEY POINT SPECIAL TEST ACT", 
                                                             "02037001" = "(02037001) FORSYTH MEM HOSP", "02037002" = "(02037002) CAPE HATTERAS NAV OCEANOGRPHI", "02037004" = "(02037004) CHERRY POINT NAVAL AVIATION DEPOT", "02039001" = "(02039001) NAVY FINANCE CENTER", 
                                                             "02039002" = "(02039002) NAVY RECRUITING AREA4 COLUMBU", "02039003" = "(02039003) NAVMAR RESCEN YOUNGSTOWN OH", "02041001" = "(02041001) COOS HEAD NAVFAC", "02042000" = "(02042000) FMSO PERSONNEL INTERN DEV CTR", 
                                                             "02042001" = "(02042001) WILLOW GROVE NAS", "02042002" = "(02042002) NAVAL SUPPLY CENTER", "02042003" = "(02042003) NAVAL BASE PHILADELPHIA", "02042004" = "(02042004) PHILADELPHIA NAVHOSP", 
                                                             "02042005" = "(02042005) NAV AIR DEV CTR WARMINSTER", "02042006" = "(02042006) NAV SHIPS PARTS CTRL CTR ICP", "02044002" = "(02044002) DAVISVILLE NCBC", "02044003" = "(02044003) NAVAL STATION NEWPORT", 
                                                             "02045001" = "(02045001) CHARLESTON NAVSTA", "02045002" = "(02045002) NAVAL HOSPITAL CHARLESTON", "02045003" = "(02045003) NV WEAPONS STATION CHARLESTON", "02047001" = "(02047001) NAVAL SUPPORT ACTIVITY MID-SOUTH", 
                                                             "02047002" = "(02047002) NAVAL WEAPONS IND RESERVE PLT", "02048001" = "(02048001) KINGSVILLE NAS", "02048002" = "(02048002) DALLAS NAS", "02048003" = "(02048003) CORPUS CHRISTI NAS", "02048004" = "(02048004) NAVY RECRUITING AREA 7 DALLAS", 
                                                             "02048005" = "(02048005) CHASE FIELD NAS", "02048006" = "(02048006) NAS JRB FT WORTH TX", "02049000" = "(02049000) NAVAL IND RESERVE ORDNANCE PL", "02051001" = "(02051001) YORKTOWN NAVWEAPSTA", "02051002" = "(02051002) NAVAL MEDICAL CTR PORTSMOUTH", 
                                                             "02051003" = "(02051003) NAVSURFWEAPCEN DAHLGREN", "02051004" = "(02051004) NORFOLK NAV SHIPYD", "02051005" = "(02051005) NORFOLK NSC", "02051006" = "(02051006) NORFOLK NAVAL BASE", "02051007" = "(02051007) LITTLE CREEK NAV AMPHIB BASE", 
                                                             "02051008" = "(02051008) OCEANA NAS", "02051009" = "(02051009) DAM NECK TRNG CTR ATLANTIC", "02051010" = "(02051010) PENTAGON - NAVY", "02051012" = "(02051012) NSGA NORTHWEST", "02053001" = "(02053001) NS BREMERTON", 
                                                             "02053002" = "(02053002) NAVAL HOSPITAL BREMERTON", "02053003" = "(02053003) PUGET SOUND NS - SAND POINT", "02053004" = "(02053004) WHIDBEY ISLAND NAS", "02053006" = "(02053006) NAVAL BASE KITSAP-BANGOR", "02053007" = "(02053007) NAVAL STATION EVERETT", 
                                                             "02054001" = "(02054001) NAV SEC GROUP DET SUGAR GROVE", "03004001" = "(03004001) YUMA MCAS", "03006001" = "(03006001) BARSTOW MCLB", "03006002" = "(03006002) CAMP PENDLETON", "03006003" = "(03006003) EL TORO MCAS", "03006004" = "(03006004) SAN DIEGO MC RECRUIT DEPOT", 
                                                             "03006005" = "(03006005) TUSTIN MCAS", "03006006" = "(03006006) USMC MOUNTAIN WARFARE TRNG CT", "03006008" = "(03006008) MCAS MIRAMAR", "03006009" = "(03006009) 29 PALMS MC AIR/GRD CMBT CTR", "03011001" = "(03011001) MARINE BARRACKS WASH D.C.", 
                                                             "03013001" = "(03013001) ALBANY MCLB", "03015001" = "(03015001) CAMP H. M. SMITH", "03015002" = "(03015002) MCBH KANEOHE BAY", "03020001" = "(03020001) 9TH MARINE CORPS DISTRICT", "03024000" = "(03024000) SOLOMONS FAC", "03029001" = "(03029001) MCSA KANSAS CITY MO", 
                                                             "03036000" = "(03036000) LAKE SENECA", "03036001" = "(03036001) 1ST MARINE CORPS DISTRICT", "03037000" = "(03037000) PALMETTO POINT", "03037001" = "(03037001) CAMP LEJEUNE MCB", "03037002" = "(03037002) CHERRY POINT MCAS", "03037003" = "(03037003) NEW RIVER MCAS", 
                                                             "03042001" = "(03042001) 4TH MARINE CORPS DISTRICT", "03045001" = "(03045001) BEAUFORT MCAS", "03045002" = "(03045002) PARRIS ISLAND MCRD", "03045003" = "(03045003) THE CITADEL", "03051001" = "(03051001) TANGIER ISLAND", "03051002" = "(03051002) HQTRS MARCORPS", 
                                                             "03051003" = "(03051003) MCCDC QUANTICO VA", "04001001" = "(04001001) BIRMINGHAM MAP AGS", "04001003" = "(04001003) DAUPHIN ISLAND AFS (CLOSED)", "04001004" = "(04001004) MAXWELL AFB (INCL. GUNTER)", "04001005" = "(04001005) HALL AGS", 
                                                             "04001008" = "(04001008) MARTIN ANGS", "04002004" = "(04002004) CAPE NEWENHAM AFS", "04002005" = "(04002005) CAPE ROMANZO AFS", "04002008" = "(04002008) EIELSON AFB", "04002009" = "(04002009) ELMENDORF AFB", "04002014" = "(04002014) KENAI ARPT", 
                                                             "04002020" = "(04002020) TATALINA AFS", "04004003" = "(04004003) COOLIDGE/FLORENCE ARPT", "04004004" = "(04004004) DAVIS-MONTHAN AFB", "04004007" = "(04004007) LUKE AFB", "04004011" = "(04004011) PHOENIX AGS", "04004013" = "(04004013) TUCSON IAP AGS", 
                                                             "04004014" = "(04004014) WILLIAMS AFB", "04005001" = "(04005001) IRA EAKER (BLYTHEVILLE) AFB", "04005002" = "(04005002) FORT SMITH MAP AGS", "04005003" = "(04005003) LITTLE ROCK AFB", "04005004" = "(04005004) HOT SPRINGS MEM FLD", 
                                                             "04006001" = "(04006001) COSTA MESA ANG STA", "04006002" = "(04006002) AF PLANT 19", "04006004" = "(04006004) LOS ANGELES AFB", "04006005" = "(04006005) ALMADEN AFS (CLOSED)", "04006006" = "(04006006) BEALE AFB", "04006007" = "(04006007) CAMBRIA AFS (CLOSED)", 
                                                             "04006008" = "(04006008) CASTLE AFB", "04006009" = "(04006009) COMPTON AGS", "04006012" = "(04006012) EDWARDS AFB", "04006014" = "(04006014) FRESNO AIR TERM AGS", "04006015" = "(04006015) GEORGE AFB (INCL. NORTON)", "04006016" = "(04006016) TRAVIS AFB", 
                                                             "04006017" = "(04006017) KLAMATH AFS", "04006020" = "(04006020) MARCH AFB", "04006022" = "(04006022) MATHER AFB", "04006023" = "(04006023) MCCLELLAN AFB", "04006024" = "(04006024) MILL VALLEY RADAR SITE", "04006025" = "(04006025) MOUNT LAGUNA AFS", 
                                                             "04006026" = "(04006026) N.HIGHLANDS AGS", "04006029" = "(04006029) NORWALK DEF FUEL SPT PT", "04006030" = "(04006030) ONTARIO IAP AGS", "04006031" = "(04006031) PILLAR POINT AFS", "04006032" = "(04006032) POINT ARENA AFS", 
                                                             "04006034" = "(04006034) SAN PEDRO HILLS RADAR SITE", "04006035" = "(04006035) ONIZUKA AFB", "04006037" = "(04006037) VAN NUYS ARPT-AGS", "04006038" = "(04006038) VANDENBERG AFB"))

data$DTY_BASE_NAME[data$DTY_BASE_NAME == ""] <- NA

## First duty base location name combined [missing = 0.503]
data$DTY_BASE_NAME <- as.character(data$DTY_BASE_NAME)
data <- data %>% dplyr::mutate(DTY_BASE_NAME.CB = dplyr::recode(data$DTY_BASE_NAME, "(01045001) FORT JACKSON" = "Fort Jackson", "(45006A) Fort Jackson" = "Fort Jackson", "(01013003) FORT BENNING" = "Fort Benning", "(13004A) Fort Benning Columbus" = "Fort Benning", 
                                                                "(01029004) FORT LEONARD WOOD" = "Fort Leonard Wood", "(29005A) Fort Leonard Wood" = "Fort Leonard Wood", "(01040003) FORT SILL" = "Fort Sill", "(40003A) Fort Sill" = "Fort Sill", 
                                                                "(01021003) FORT KNOX" = "Fort Knox", "(21002A) Fort Knox" = "Fort Knox", "(01051008) FORT LEE" = "Fort Lee", "(51012A) Fort Lee" = "Fort Lee", "(01013004) FORT GORDON" = "Fort Gordon", 
                                                                "(13006A) Fort Gordon" = "Fort Gordon", "(01048007) FORT HOOD" = "Fort Hood", "(48012A) Fort Hood" = "Fort Hood", "(01048008) FORT SAM HOUSTON" = "Fort Sam Houston", 
                                                                "(48013A) Fort Sam Houston San Antonio" = "Fort Sam Houston", "(01037002) FORT BRAGG" = "Fort Bragg", "(37008A) Fort Bragg" = "Fort Bragg", "(01021002) FORT CAMPBELL" = "Fort Campbell", 
                                                                "(21001A) Fort Campbell" = "Fort Campbell", "(01051006) FORT EUSTIS" = "Fort Eustis", "(51011A) Fort Eustis" = "Fort Eustis", "(01013007) FORT STEWART" = "Fort Stewart", 
                                                                "(13008A) Fort Stewart" = "Fort Stewart", "(01024002) ABERDEEN PROVING GROUND" = "Aberdeen Proving Ground", "(24001A) Aberdeen Proving Ground" = "Aberdeen Proving Ground", 
                                                                "(01004002) FORT HUACHUCA" = "Fort Huachuca", "(04003A) Fort Huachuca" = "Fort Huachuca", "(01053003) FORT LEWIS" = "Fort Lewis", "(53007A) Fort Lewis" = "Fort Lewis", 
                                                                "(01048003) FORT BLISS" = "Fort Bliss", "(48011A) Fort Bliss" = "Fort Bliss", "(01008002) FORT CARSON" = "Fort Carson", "(08004A) Fort Carson" = "Fort Carson", "(01001011) FORT RUCKER" = "Fort Rucker", 
                                                                "(01007A) Fort Rucker" = "Fort Rucker", "(04048017) LACKLAND AFB" = "Lackland AFB", "(01036009) WEST POINT MILRES" = "West Point Military Reservation", 
                                                                "(36024A) West Point Military Reservation" = "West Point Military Reservation", "(01020004) FORT RILEY" = "Fort Riley", "(20005A) Fort Riley" = "Fort Riley", "(01036002) FORT DRUM" = "Fort Drum", 
                                                                "(36007A) Fort Drum" = "Fort Drum", "(01001010) REDSTONE ARSENAL" = "Redstone Arsenal", "(01013A) Redstone Arsenal Huntsville" = "Redstone Arsenal", "(01002002) FORT RICHARDSON" = "Fort Richardson", 
                                                                "(02007A) Fort Richardson" = "Fort Richardson", "(01002003) FORT JONATHAN WAINWRIGHT" = "Fort Jonathan Wainwright", "(02006A) Fort Jonathan Wainwright Fairbanks" = "Fort Jonathan Wainwright", 
                                                                "(01004004) YUMA PROVING GROUND" = "Yuma Proving Ground", "(04010A) Yuma Proving Ground" = "Yuma Proving Ground", "(01006005) FORT IRWIN" = "Fort Irwin", "(06021A) Fort Irwin" = "Fort Irwin", 
                                                                "(01006008) LOS ALAMITOS AFRC" = "Los Alamitos AFRC", "(01006010) PRESIDIO OF MONTEREY" = "Presidio of Monterey", "(06056A) Presidio of Monterey" = "Presidio of Monterey", 
                                                                "(01006014) SACRAMENTO ARMY DEPOT" = "Sacramento Army Depot", "(01011001) FORT LESLIE J MCNAIR" = "Fort Leslie J McNair", "(11004A) Fort Leslie J McNair" = "Fort Leslie J McNair", 
                                                                "(01011002) WALTER REED ARMY MED CTR" = "Walter Reed Army Medical Center", "(11007A) Walter Reed Army Medical Center Washington" = "Walter Reed Army Medical Center", 
                                                                "(01015013) FORT SHAFTER" = "Fort Shafter", "(15003A) Fort Shafter Honolulu" = "Fort Shafter", "(01015014) SCHOFIELD BARRACKS" = "Schofield Barracks", 
                                                                "(01015015) TRIPLER ARMY MEDICAL CENTER" = "Tripler Army Medical Center", "(01017003) ROCK ISLAND ARSENAL" = "Rock Island Arsenal", "(17009A) Rock Island Arsenal" = "Rock Island Arsenal", 
                                                                "(01018001) FORT BENJAMIN HARRISON" = "Fort Benjamin Harrison", "(18003A) Fort Benjamin Harrison" = "Fort Benjamin Harrison", "(01020003) FORT LEAVENWORTH" = "Fort Leavenworth", 
                                                                "(20004A) Fort Leavenworth" = "Fort Leavenworth", "(01022003) FORT POLK" = "Fort Polk", "(22006A) Fort Polk" = "Fort Polk", "(01024004) FORT DETRICK" = "Fort Detrick", 
                                                                "(24005A) Fort Detrick Lewistown" = "Fort Detrick", "(01024006) FORT GEORGE G. MEADE" = "Fort George G Meade", "(24006A) Fort George G Meade" = "Fort George G Meade", 
                                                                "(01028003) CAMP SHELBY" = "Camp Shelby", "(28003A) Camp Shelby Hattiesburg" = "Camp Shelby", "(01034001) FORT DIX" = "Fort Dix", "(34002A) Fort Dix" = "Fort Dix", 
                                                                "(01035001) WHITE SANDS MISSILE RANGE" = "White Sands Missile Range", "(35006A) White Sands Missile Range" = "White Sands Missile Range", "(01042002) CARLISLE BARRACKS" = "Carlisle Barracks", 
                                                                "(42002A) Carlisle Barracks" = "Carlisle Barracks", "(01042009) TOBYHANNA ARMY DEPOT" = "Tobyhanna Army Depot", "(01051003) FORT BELVOIR" = "Fort Belvoir", "(01051007) FORT STORY" = "Fort Story", 
                                                                "(51015A) Fort Story" = "Fort Story", "(01051010) FORT MYER" = "Fort Myer", "(51014A) Fort Myer" = "Fort Myer", "(01055003) FORT MCCOY" = "Fort McCoy", "(55003A) Fort McCoy Sparta" = "Fort McCoy", 
                                                                "(02012003) CORRY STATION NTTC" = "Corry Station NTTC", "(02015005) NAVAL BASE PEARL HARBOR" = "Naval Base Pearl Harbor", "(02017001) NAVAL STATION GREAT LAKES" = "Naval Station Great Lakes", 
                                                                "(02024002) ANNAPOLIS NS(INCL USNA)" = "Annapolis NS", "(02024004) NNMC BETHESDA" = "NNMC Bethesda", "(02024007) WHITE OAK NSWC DAHLGREN" = "White Oak NSWC Dahlgren", 
                                                                "(02051001) YORKTOWN NAVWEAPSTA" = "Yorktown Naval Weapons Station", "(02051006) NORFOLK NAVAL BASE" = "Norfolk Naval Base", "(02051007) LITTLE CREEK NAV AMPHIB BASE" = "Little Creek Naval Base", 
                                                                "(04002009) ELMENDORF AFB" = "Elmendorf AFB", "(04008001) BUCKLEY AGB" = "Buckley AGB", "(04008002) PETERSON AFB" = "Peterson AFB", "(04008003) SCHRIEVER AFB" = "Schriever AFB", 
                                                                "(04010001) DOVER AFB" = "Dover AFB", "(04012004) EGLIN AFB" = "Eglin AFB", "(04015001) HICKAM AFB" = "Hickman AFB", "(04045006) SHAW AFB" = "Shaw AFB", 
                                                                "(04048013) GOODFELLOW AFB" = "Goodfellow AFB", "(04048026) SHEPPARD AFB" = "Sheppard AFB", "(05039001) COLUMBUS DEF DEPOT" = "Columbus Defense Depot", "(39003D) Columbus Defense Depot" = "Columbus Defense Depot", 
                                                                "(08051002) USCG ALEXANDRIA VA" = "Cameron Station Alexandria", "(51003D) Cameron Station Alexandria" = "Cameron Station Alexandria", "(05005A) Pine Bluff Arsenal" = " arraarveyennr HBarraB nr Bluff", 
                                                                "(06023A) Fort Ord" = "Fort Ord", "(06073D) Tracy Defense Depot Stockton" = "Tracy Defense Depot Stockton", "(11003D) DFAS Headquarters Washington" = "Columbus Defense Depot", 
                                                                "(11006D) Ntl Imagery and Mapping Agcy Hydro/Topographc Ctr Washingtn" = "Ntl Imagery And Mapping Agcy Hydro/Topographc Ctr Washingtn", "(13005A) Fort Gillem Forest Park" = "Fort Gillem Forest Park", 
                                                                "(13007A) Fort McPherson" = "Fort McPherson", "(17003A) Fort Sheridan" = "Fort Sheridan", "(19002A) Fort Des Moines" = "Fort Des Moines", "(19004A) Fort Snelling Fort Dodge" = "Fort Snelling Fort Dodge", 
                                                                "(22009A) New Orleans Military Ocean Terminal" = "New Orleans Military Ocean Terminal", "(25005A) Fort Devens" = "Fort Devens", "(25007A) Natick Army Research and Development Center" = "Natick Army Research And Development Center", 
                                                                "(26002A) Detroit Arsenal Warren" = "Detroit Arsenal Warren", "(34003A) Fort Monmouth" = "Fort Monmouth", "(42003A) Charles Kelly Support Facility Noblestown" = "Charles Kelly Support Facility Noblestown", 
                                                                "(42009A) New Cumberland Army Depot" = "New Cumberland Army Depot", "(42015A) Scranton Army Ammunition Plant" = "Scranton Army Ammunition Plant", "(51008A) Department of the Army Activities Pentagon" = "Pentagon", 
                                                                "(51013A) Fort Monroe Hampton" = "Fort Monroe", "(51022D) Department of Defense Activities Pentagon" = "Pentagon", "(67001A) Johnston Atoll" = "Johnston Atoll", "(BE001A) Chievres Army Station" = "Chievres Army Station", 
                                                                "(BE002A) Florennes" = "Florennes", "(EG002A) El Gorah" = "El Gorah", "(GM003A) Armstrong Barracks Buedingen" = "Armstrong Barracks Buedingen", "(GM004A) Aschaffenburg" = "Aschaffenburg", 
                                                                "(GM005A) Babenbausen Kaserne" = "Babenbausen Kaserne", "(GM007A) Bad Kreuznach" = "Bad Kreuznach", "(GM008A) Barton Barracks Ansbach" = "Barton Barracks Ansbach", "(GM013A) Butzbach" = "Butzbach", 
                                                                "(GM014A) Campbell Barracks Heidelberg" = "Campbell Barracks Heidelberg", "(GM016A) Conn Barracks Schweinfurt" = "Conn Barracks Schweinfurt", "(GM018A) Darmstadt" = "Darmstadt", 
                                                                "(GM019A) Dexheim Military Community" = "Dexheim Military Community", "(GM021A) Field Station Bad Aibling" = "Field Station Bad Aibling", "(GM024A) Frankfurt" = "Frankfurt", "(GM025A) Friedberg" = "Friedberg", 
                                                                "(GM027A) Furth" = "Furth", "(GM029A) Garmisch" = "Garmisch", "(GM031A) Gelnhausen" = "Gelnhausen", "(GM034A) Giebelstadt" = "Giebelstadt", "(GM035A) Giessen" = "Giessen", "(GM037A) Grafenwohr" = "Grafenwohr", 
                                                                "(GM038A) H D Smith Barracks Baumholder" = "H D Smith Barracks Baumholder", "(GM040A) Hanau" = "Hanau", "(GM041A) Harvey Barracks Kitzingen" = "Harvey Barracks Kitzingen", "(GM042A) Heidelberg" = "Heidelberg", 
                                                                "(GM046A) Hindenburg Kaserne Ansbach" = "Hindenburg Kaserne Ansbach", "(GM047A) Hohenfels" = "Hohenfels", "(GM049A) Illesheim" = "Illesheim", "(GM051A) Kaefertal" = "Kaefertal", "(GM052A) Kaiserslautern" = "Kaiserslautern", 
                                                                "(GM054A) Karlsruhe" = "Karlsruhe", "(GM055A) Katterbach Kaserne" = "Katterbach Kaserne", "(GM057A) Kirchgoens" = "Kirchgoens", "(GM058A) Landstuhl Medical Center" = "Landstuhl Medical Center", 
                                                                "(GM059A) Larson Barracks Kitzingen" = "Larson Barracks Kitzingen", "(GM060A) Ledward Barracks Schweinfurt" = "Ledward Barracks Schweinfurt", "(GM064A) Mainz" = "Mainz", "(GM065A) Mannheim" = "Mannheim", 
                                                                "(GM068A) Miesau Army Depot" = "Miesau Army Depot", "(GM070A) Nellingen" = "Nellingen", "(GM073A) Nurnburg" = "Nurnburg", "(GM075A) Panzer Kaserne Boblingen" = "Panzer Kaserne Boblingen", 
                                                                "(GM076A) Patch Barracks Vaihingen" = "Patch Barracks Vaihingen", "(GM077A) Patton Barracks Heidelberg" = "Patton Barracks Heidelberg", "(GM080A) Pirmasens" = "Pirmasens", "(GM083A) Reese Barracks Augsburg" = "Reese Barracks Augsburg", 
                                                                "(GM087A) Rose Barracks Bad Kreuznach" = "Rose Barracks Bad Kreuznach", "(GM088A) Sandhofen" = "Sandhofen", "(GM092A) Schwetzingen" = "Schwetzingen", "(GM099A) Stuttgart" = "Stuttgart", 
                                                                "(GM102A) Tompkin Barracks Schwetzingen" = "Tompkin Barracks Schwetzingen", "(GM103A) Viseck" = "Viseck", "(GM104A) Warner Barracks Bamberg" = "Warner Barracks Bamberg", "(GM108A) Worms" = "Worms", 
                                                                "(GM109A) Wuerzberg" = "Wuerzberg", "(IT004A) Camp Darby Livorno" = "Camp Darby Livorno", "(IT012A) Vicenza" = "Vicenza", "(JA003A) Camp Zama Tokyo" = "Camp Zama Tokyo", "(JA011A) Torii Station Okinawa" = "Torii Station Okinawa", 
                                                                "(KS001A) 19th Support Command Camp Henry Taegu" = "19th Support Command Camp Henry Taegu", "(KS003A) 23rd Area Support Group Camp Humphreys" = "23rd Area Support Group Camp Humphreys", 
                                                                "(KS004A) 34th Area Support Group Pusan" = "34th Area Support Group Pusan", "(KS006A) Camp Casey Tongduchon" = "Camp Casey Tongduchon", "(KS007A) Camp Long Wongju Kangwon-Bo" = "Camp Long Wongju Kangwon-Bo", 
                                                                "(KS008A) Camp Market Bupyeong" = "Camp Market Bupyeong", "(KS009A) Camp Red Cloud Uijonbu" = "Camp Red Cloud Uijonbu", "(KS015A) Seoul" = "Seoul", "(KS019A) Yongsan" = "Yongsan", 
                                                                "(KU001A) Combat Support Kuwait City" = "Combat Support Kuwait City", "(NL001A) Brunssum" = "Brunssum", "(SA005A) Riyadh" = "Riyadh", "01011F" = "01011F", "04009M" = "04009M", "06009M" = "06009M", "06032F" = "06032F", 
                                                                "06040N" = "06040N", "06055N" = "06055N", "06066N" = "06066N", "09004N" = "09004N", "11005N" = "11005N", "12003N" = "12003N", "12004F" = "12004F", "12010F" = "12010F", "12020F" = "12020F", "13016F" = "13016F", "15001N" = "15001N", 
                                                                "15004F" = "15004F", "15006N" = "15006N", "15007N" = "15007N", "17006N" = "17006N", "17012F" = "17012F", "24011N" = "24011N", "26009F" = "26009F", "34005N" = "34005N", "36009F" = "36009F", "36018N" = "36018N", "39014F" = "39014F", 
                                                                "40005F" = "40005F", "41003F" = "41003F", "42008N" = "42008N", "46002F" = "46002F", "47008N" = "47008N", "48016F" = "48016F", "48017F" = "48017F", "48018N" = "48018N", "48020F" = "48020F", "48024N" = "48024N", "48030F" = "48030F", 
                                                                "51004N" = "51004N", "51016F" = "51016F", "51017N" = "51017N", "51018N" = "51018N", "53010N" = "53010N", "66002F" = "66002F", "72001N" = "72001N", "BE003F" = "BE003F", "CU003N" = "CU003N", "GM082F" = "GM082F", "GM106F" = "GM106F", 
                                                                "IC002N" = "IC002N", "IT009N" = "IT009N", "KS002F" = "KS002F", "KS014F" = "KS014F", "KS016F" = "KS016F", "TU004F" = "TU004F", "UK001F" = "UK001F", "UK004F" = "UK004F", "1107002" = "1107002", "1107003" = "1107003", "1107014" = "1107014", 
                                                                "1107018" = "1107018", "1107022" = "1107022", "1107023" = "1107023", "1107034" = "1107034", "1107042" = "1107042", "1107061" = "1107061", "1107064" = "1107064", "1107079" = "1107079", "1107081" = "1107081", "1107089" = "1107089", 
                                                                "1128002" = "1128002", "1131001" = "1131001", "1131002" = "1131002", "1135001" = "1135001", "1135003" = "1135003", "1135004" = "1135004", "1135005" = "1135005", "1135007" = "1135007", "1135011" = "1135011", "2090001" = "2090001", 
                                                                "2128001" = "2128001", "4065002" = "4065002", "4107001" = "4107001", "4107002" = "4107002", "4107011" = "4107011", "4135001" = "4135001", "4135002" = "4135002", "4135003" = "4135003", "7051001" = "7051001"))

data$DTY_BASE_NAME.CB[data$DTY_BASE_NAME.CB == ""] <- NA

## PULHES: P = Physical Condition, U = Upper Extremities, L = Lower Extremities, H = Hearing, E = Eyes, S = Psychiatric [lower numbers better]
# De-catinate
data <- data %>% dplyr::mutate(PULHES.P = substr(data$PULHES, 1, 1))
data <- data %>% dplyr::mutate(PULHES.U = substr(data$PULHES, 2, 2))
data <- data %>% dplyr::mutate(PULHES.L = substr(data$PULHES, 3, 3))
data <- data %>% dplyr::mutate(PULHES.H = substr(data$PULHES, 4, 4))
data <- data %>% dplyr::mutate(PULHES.E = substr(data$PULHES, 5, 5))
data <- data %>% dplyr::mutate(PULHES.S = substr(data$PULHES, 6, 6))
# Remove blanks
data$PULHES.P[data$PULHES.P == ""] <- NA
data$PULHES.U[data$PULHES.U == ""] <- NA
data$PULHES.L[data$PULHES.L == ""] <- NA
data$PULHES.H[data$PULHES.H == ""] <- NA
data$PULHES.E[data$PULHES.E == ""] <- NA
data$PULHES.S[data$PULHES.S == ""] <- NA
# Convert to integer
data$PULHES.P <- as.integer(data$PULHES.P)
data$PULHES.U <- as.integer(data$PULHES.U)
data$PULHES.L <- as.integer(data$PULHES.L)
data$PULHES.H <- as.integer(data$PULHES.H)
data$PULHES.E <- as.integer(data$PULHES.E)
data$PULHES.S <- as.integer(data$PULHES.S)
# De-catinate
data$PHY_CPCY_PHY_PRFL_MOD_CD <- substr(data$PHY_CPCY_PHY_PRFL_MOD_CD, 1, 1)
data$UXTR_PHY_PRFL_MOD_CD <- substr(data$UXTR_PHY_PRFL_MOD_CD, 1, 1)
data$LXTR_PHY_PRFL_MOD_CD <- substr(data$LXTR_PHY_PRFL_MOD_CD, 1, 1)
data$HRG_PHY_PRFL_MOD_CD <- substr(data$HRG_PHY_PRFL_MOD_CD, 1, 1)
data$VSN_PHY_PRFL_MOD_CD <- substr(data$VSN_PHY_PRFL_MOD_CD, 1, 1)
data$PSYC_PHY_PRFL_MOD_CD <- substr(data$PSYC_PHY_PRFL_MOD_CD, 1, 1)
# Remove blanks
data$PHY_CPCY_PHY_PRFL_MOD_CD[data$PHY_CPCY_PHY_PRFL_MOD_CD == ""] <- NA
data$UXTR_PHY_PRFL_MOD_CD[data$UXTR_PHY_PRFL_MOD_CD == ""] <- NA
data$LXTR_PHY_PRFL_MOD_CD[data$LXTR_PHY_PRFL_MOD_CD == ""] <- NA
data$HRG_PHY_PRFL_MOD_CD[data$HRG_PHY_PRFL_MOD_CD == ""] <- NA
data$VSN_PHY_PRFL_MOD_CD[data$VSN_PHY_PRFL_MOD_CD == ""] <- NA
data$PSYC_PHY_PRFL_MOD_CD[data$PSYC_PHY_PRFL_MOD_CD == ""] <- NA
# Convert to integer
data$PHY_CPCY_PHY_PRFL_MOD_CD <- as.integer(data$PHY_CPCY_PHY_PRFL_MOD_CD)
data$UXTR_PHY_PRFL_MOD_CD <- as.integer(data$UXTR_PHY_PRFL_MOD_CD)
data$LXTR_PHY_PRFL_MOD_CD <- as.integer(data$LXTR_PHY_PRFL_MOD_CD)
data$HRG_PHY_PRFL_MOD_CD <- as.integer(data$HRG_PHY_PRFL_MOD_CD)
data$VSN_PHY_PRFL_MOD_CD <- as.integer(data$VSN_PHY_PRFL_MOD_CD)
data$PSYC_PHY_PRFL_MOD_CD <- as.integer(data$PSYC_PHY_PRFL_MOD_CD)
# Coalesce
data$PULHES.P.CB <- dplyr::coalesce(data$PHY_CPCY_PHY_PRFL_MOD_CD, data$PULHES.P)
data$PULHES.U.CB <- dplyr::coalesce(data$UXTR_PHY_PRFL_MOD_CD, data$PULHES.U)
data$PULHES.L.CB <- dplyr::coalesce(data$LXTR_PHY_PRFL_MOD_CD, data$PULHES.L)
data$PULHES.H.CB <- dplyr::coalesce(data$HRG_PHY_PRFL_MOD_CD, data$PULHES.H)
data$PULHES.E.CB <- dplyr::coalesce(data$VSN_PHY_PRFL_MOD_CD, data$PULHES.E)
data$PULHES.S.CB <- dplyr::coalesce(data$PSYC_PHY_PRFL_MOD_CD, data$PULHES.S)
# Empty values to NA
data$PULHES.P.CB[data$PULHES.P.CB == 0] <- NA
data$PULHES.U.CB[data$PULHES.U.CB == 0] <- NA
data$PULHES.L.CB[data$PULHES.L.CB == 0] <- NA
data$PULHES.H.CB[data$PULHES.H.CB == 0] <- NA
data$PULHES.E.CB[data$PULHES.E.CB == 0] <- NA
data$PULHES.S.CB[data$PULHES.S.CB == 0] <- NA
# PULHES Total
data$PULHES.TOTAL <- data %>% dplyr::select(PULHES.P.CB, PULHES.U.CB, PULHES.L.CB, PULHES.H.CB, PULHES.E.CB, PULHES.S.CB) %>% rowSums(na.rm = TRUE)
# Wrong values to NA
data$PULHES.TOTAL[data$PULHES.TOTAL == 0] <- NA
data$PULHES.TOTAL[data$PULHES.TOTAL == 1] <- NA
data$PULHES.TOTAL[data$PULHES.TOTAL == 2] <- NA
data$PULHES.TOTAL[data$PULHES.TOTAL == 3] <- NA
data$PULHES.TOTAL[data$PULHES.TOTAL == 4] <- NA
data$PULHES.TOTAL[data$PULHES.TOTAL == 5] <- NA
# PULHES MEAN
data <- data %>% dplyr::mutate(PULHES.MEAN = rowMeans(data[c("PULHES.P.CB", "PULHES.U.CB", "PULHES.L.CB", "PULHES.H.CB", "PULHES.E.CB", "PULHES.S.CB")], na.rm = TRUE))

## Height [missing = 0.235]
data$HEIGHT <- as.integer(data$HEIGHT)
data$HEIGHT[data$HEIGHT == 0] <- NA
data$HGT_DM[data$HGT_DM == 0] <- NA
data$HEIGHT.CB <- dplyr::coalesce(data$HGT_DM, data$HEIGHT)

## Weight [missing = 0.235]
data$WEIGHT[data$WEIGHT == 0] <- NA
data$PN_WGHT_QY[data$PN_WGHT_QY == 0] <- NA
data$WEIGHT.CB <- dplyr::coalesce(data$PN_WGHT_QY, data$WEIGHT)

## Prior Service [missing = 0.046]
data$PS <- as.character(data$PS)
data$PS[data$PS == ""] <- NA
data$MEP_PRIOR_SVC_IND_CD <- as.character(data$MEP_PRIOR_SVC_IND_CD)
data$MEP_PRIOR_SVC_IND_CD[data$MEP_PRIOR_SVC_IND_CD == ""] <- NA

data$PS.CB <- dplyr::coalesce(data$PS, data$MEP_PRIOR_SVC_IND_CD)
data$PS.CB <- factor(data$PS.CB)

## Accession Date [missing = 0.0017]
# DATE_ACC (accession date for enlisted), FILE_DT (first date of filing), AFMS_BASE_DT (accounts for first date of military service; i.e years before 2000 will be present)
data$DATE_ACC <- lubridate::as_date(data$DATE_ACC)
data$AFMS_BASE_DT <- lubridate::as_date(data$AFMS_BASE_DT)
data$USVC_INIT_ENT_DT <- lubridate::as_date(data$USVC_INIT_ENT_DT)
data$DATE_ACC.CB <- dplyr::coalesce(data$DATE_ACC, data$AFMS_BASE_DT, data$USVC_INIT_ENT_DT)
#sum(is.na(data$DATE_ACC.CB))/length(data$PID_PDE)
# Ensure accession dates line up
data <- data %>% filter(DATE_ACC.CB >= "2000-01-01") # N = 1,440,701
## Accession Year [missing = 0.00]
data <- data %>% mutate(YEAR_ACC.CB = format(DATE_ACC.CB, "%Y"))

## create age of Soldier at accesion date based on birth date
agefilter <- data %>% dplyr::select(PID_PDE, DATE_BIRTH.CB, DATE_ACC.CB) %>% na.omit()
agefilter$AGE_ACC <- eeptools::age_calc(agefilter$DATE_BIRTH.CB, agefilter$DATE_ACC.CB, units = "years", precise = TRUE)
agefilter <- agefilter %>% dplyr::select(PID_PDE, AGE_ACC)
data <- data %>% dplyr::left_join(agefilter, by = "PID_PDE") # duplicates in age filter adding duplicate rows

## New Education varaiable with reduced categories
# Create reduced category education by copying education variable
rcs8 <- "11=1; 12=1; 13=1; 14=1; 21=2; 22=2; 23=2; 24=1; 25=2; 26=2; 27=2; 28=9; 31=2; 32=1; 41=3; 42=3; 43=3; 44=4;
              45=4; 46=3; 51=5; 52=6; 61=7; 62=7; 63=8; 64=8; 65=8; 99=9; else=NA" # Eigth coding scheme
data <- data %>% dplyr::mutate(EDU_LVL_RE = data$EDU_LVL_CD)
# Recode education levels
data <- ryouready::recode2(data, vars = c("EDU_LVL_RE"), recodes = rcs8)
data <- data %>% dplyr::mutate(EDU_LVL_RE_last = data$EDU_LVL_CD_last)
# Recode education levels
data <- ryouready::recode2(data, vars = c("EDU_LVL_RE_last"), recodes = rcs8)
## Discharge to binary honorale/dishonorable
# Create reduced category education by copying education variable
data <- data %>% mutate(CHAR_SVC_CD2 = data$CHAR_SVC_CD)
# Recode discharge levels
data$CHAR_SVC_CD2 <- data$CHAR_SVC_CD2 %>% dplyr::recode("A" = 1, "B" = 1, "H" = 1, "J" = 1, "D" = 0, "E" = 0, "K" = 0, "F" = 0) 
# recode seperation code
data <- data %>% dplyr::mutate(SEP_CD.CB = dplyr::recode(data$ISVC_SEP_CD, "1000" = "(1000) Unknown or not applicable", "1001" = "(1001) Expiration of term of service", "1002" = "(1002) Early release, insufficient retainability", 
                                                         "1003" = "(1003) Early release, to attend school", "1004" = "(1004) Early release, police duty", "1005" = "(1005) Early release, in the national interest", "1006" = "(1006) Early release, seasonal employment", 
                                                         "1007" = "(1007) Early release, to teach", "1008" = "(1008) Early release, other, including RIF, VSI, and SSB", "1010" = "(1010) Condition existing prior to service", "1011" = "(1011) Disability, severance pay", 
                                                         "1012" = "(1012) Permanent disability retirement", "1013" = "(1013) Temporary disability retirement", "1014" = "(1014) Disability, not existng prior to service, no severance pay", 
                                                         "1015" = "(1015) Disability, Title 10 USC retirement", "1016" = "(1016) Unqualified for active duty, other", "1017" = "(1017) Failure to meet weight or body fat standards", "1022" = "(1022) Dependency or hardship", 
                                                         "1030" = "(1030) Death, battle casualty", "1031" = "(1031) Death, non-battle, disease", "1032" = "(1032) Death, non-battle, other", "1033" = "(1033) Death, cause not specified", "1040" = "(1040) Officer commissioning program", 
                                                         "1041" = "(1041) Warrant officer program", "1042" = "(1042) Military service academy", "1050" = "(1050) Retirement, 20 to 30 years of service", "1051" = "(1051) Retirement, over 30 years of service", 
                                                         "1052" = "(1052) Retirement, other", "1060" = "(1060) Character or behavior disorder", "1061" = "(1061) Motivational problems (apathy)", "1062" = "(1062) Enuresis", "1063" = "(1063) Inaptitude", "1064" = "(1064) Alcoholism", 
                                                         "1065" = "(1065) Discreditable incidents, civilian or military", "1066" = "(1066) Shirking", "1067" = "(1067) Drugs", "1068" = "(1068) Financial Irresponsibility", "1069" = "(1069) Lack of dependent support", 
                                                         "1070" = "(1070) Unsanitary habits", "1071" = "(1071) Civil court conviction", "1072" = "(1072) Security", "1073" = "(1073) Court-martial", "1074" = "(1074) Fraudulent entry", "1075" = "(1075) AWOL or desertion", 
                                                         "1076" = "(1076) Homosexuality", "1077" = "(1077) Sexual perversion", "1078" = "(1078) Good of the service (discharge in lieu of court-martial)", "1079" = "(1079) Juvenile offender", "1080" = "(1080) Misconduct, reason unknown", 
                                                         "1081" = "(1081) Unfitness, reason unknown", "1082" = "(1082) Unsuitability, reason unknown", "1083" = "(1083) Pattern of minor disciplinary infractions", "1084" = "(1084) Commission of a serious offense", 
                                                         "1085" = "(1085) Failure to meet minimum qualifications for retention", "1086" = "(1086) Unsat performance (former Expeditious Discharge Program)", "1087" = "(1087) Entry lev perform and conduct (former Trainee Dschrge Progm)", 
                                                         "1088" = "(1088) Unsatisfactory performance of Ready Reserve obligation", "1090" = "(1090) Secretarial authority", "1091" = "(1091) Erroneous enlistment or induction", "1092" = "(1092) Sole surviving family member", 
                                                         "1093" = "(1093) Marriage", "1094" = "(1094) Pregnancy", "1095" = "(1095) Minority (underage)", "1096" = "(1096) Conscientious objector", "1097" = "(1097) Parenthood", "1098" = "(1098) Breach of contract", 
                                                         "1099" = "(1099) Other", "1100" = "(1100) Immediate reenlistment", "1101" = "(1101) Dropped from strength, desertion", "1102" = "(1102) Dropped from strength, imprisonment", "1103" = "(1103) Record correction", 
                                                         "1104" = "(1104) Dropped from strength, MIA or POW", "1105" = "(1105) Dropped from strength, other", "2000" = "(2000) Unknown or not applicable", "2001" = "(2001) Expiration of term of service", 
                                                         "2002" = "(2002) Voluntary release, to attend school or to teach", "2003" = "(2003) Voluntary release, in the national interest", "2004" = "(2004) Voluntary release, unqualified resignation", 
                                                         "2005" = "(2005) Voluntary release, other, including VSI and SSB", "2006" = "(2006) Invol release, temp officer reverts to enlisted status", "2007" = "(2007) Involuntary release, maximum age or service", 
                                                         "2008" = "(2008) Involuntary release, convenience of the government", "2009" = "(2009) Involuntary release, other", "2010" = "(2010) Condition existing prior to service", "2011" = "(2011) Disability, severance pay", 
                                                         "2012" = "(2012) Permanent disability retirement", "2013" = "(2013) Temporary disability retirement", "2015" = "(2015) Disability, Title 10 USC retirement", "2016" = "(2016) Unqualified for active duty, other", 
                                                         "2017" = "(2017) Failure to meet weight or body fat standards", "2022" = "(2022) Dependency or hardship", "2030" = "(2030) Death, battle casualty", "2031" = "(2031) Death, non-battle, disease", 
                                                         "2032" = "(2032) Death, non-battle, other", "2033" = "(2033) Death, cause not specified", "2050" = "(2050) Retirement, 20 to 30 years of service", "2051" = "(2051) Retirement, over 30 years of service", 
                                                         "2052" = "(2052) Retirement, other", "2053" = "(2053) Retirement, failure of selection for promotion", "2060" = "(2060) Character or behavior disorder", "2061" = "(2061) Motivational problems (apathy)", 
                                                         "2063" = "(2063) Failure of course of instruction", "2064" = "(2064) Alcoholism", "2065" = "(2065) Discreditable incidents, civilian or military", "2067" = "(2067) Drugs", "2068" = "(2068) Financial Irresponsibility", 
                                                         "2071" = "(2071) Civil court conviction", "2072" = "(2072) Security", "2073" = "(2073) Court-martial", "2074" = "(2074) Fraudulent entry", "2075" = "(2075) AWOL or desertion", "2076" = "(2076) Homosexuality", 
                                                         "2077" = "(2077) Sexual perversion", "2078" = "(2078) Good of the service (discharge in lieu of court-martial)", "2079" = "(2079) Failure of selection for promotion", "2080" = "(2080) Unsuitability, other", 
                                                         "2081" = "(2081) Unfitness or unacceptable conduct, other", "2083" = "(2083) Pattern of minor disciplinary infractions", "2084" = "(2084) Commission of a serious offense", 
                                                         "2085" = "(2085) Failure to meet minimum retention requirements", "2090" = "(2090) Secretarial authority", "2091" = "(2091) Erroneous enlistment or induction", "2092" = "(2092) Sole surviving family member", 
                                                         "2093" = "(2093) Marriage", "2094" = "(2094) Pregnancy", "2095" = "(2095) Minority (underage)", "2096" = "(2096) Conscientious objector", "2097" = "(2097) Parenthood", "2098" = "(2098) Breach of contract", 
                                                         "2099" = "(2099) Other", "2100" = "(2100) Change in status", "2101" = "(2101) Dropped from strength, desertion", "2102" = "(2102) Dropped from strength, imprisonment", "2103" = "(2103) Record correction", 
                                                         "2104" = "(2104) Dropped from strength, MIA or POW", "2105" = "(2105) Dropped from strength, other"))

data$SEP_CD.CB[data$SEP_CD.CB == ""] <- NA

# Transaction code variable [missing = 0.057)]
data$ADP_TXN_TYP_CD <- as.character(data$ADP_TXN_TYP_CD)
data <- data %>% dplyr::mutate(TRANS_TYPE.CB = dplyr::recode(data$ADP_TXN_TYP_CD, "001" = "(001) Social Security Number Correction", "002" = "(002) Name Change", 
                                                             "003" = "(003) Payplan and/or Grade Change", "004" = "(004) Assigned and/or Duty Unit Change", "110" = "(110) Generated Gain", "111" = "(111) Gain", 
                                                             "112" = "(112) Gain Non Prior Service", "115" = "(115) Gain Prior Service Reserve", "117" = "(117) Gain Prior Service Retired", 
                                                             "118" = "(118) Gain Prior Service Delayed Enlistment Program", "119" = "(119) Gain Prior Service from Enlisted to Officer", "120" = "(120) Gain Prior Service Military Control", 
                                                             "123" = "(123) Gain Prior Service Other", "130" = "(130) Generated Loss", "131" = "(131) Loss", "132" = "(132) Loss to Civilian Life", "135" = "(135) Loss to Reserve Duty", 
                                                             "137" = "(137) Loss to Retired", "138" = "(138) Loss to Death", "139" = "(139) Loss from Enlisted to Officer", "140" = "(140) Loss Drop from Military Control", 
                                                             "151" = "(151) Immediate Reenlistment", "152" = "(152) Extension", "999" = "(999) Unknown, pending, or replaced by amended data"))
data$TRANS_TYPE.CB[data$TRANS_TYPE.CB == ""] <- NA
# Create reduced transaction code variable
data <- data %>% dplyr::mutate(TRANS_TYPE_RE.CB = dplyr::recode(data$ADP_TXN_TYP_CD, "001" = "ADMIN", "002" = "ADMIN", "003" = "ADMIN", "004" = "ADMIN", "110" = "GAIN", "111" = "GAIN", "112" = "GAIN", 
                                                                "115" = "GAIN", "117" = "GAIN", "118" = "GAIN", "119" = "GAIN", "120" = "GAIN", "123" = "GAIN", "130" = "LOSS", "131" = "LOSS", "132" = "LOSS", "135" = "LOSS", "137" = "LOSS", 
                                                                "138" = "LOSS", "139" = "LOSS", "140" = "LOSS", "151" = "LOSS", "152" = "LOSS", "999" = "ADMIN"))
data$TRANS_TYPE_RE.CB[data$TRANS_TYPE_RE.CB == ""] <- NA

## create length of service variable [ADSVC_PE_DT missing: overall = 0.121, enlisted = .0804, officer = 0.7843]
data$ADSVC_PE_DT <-lubridate::as_date(data$ADSVC_PE_DT)
data$DATE_ACC.CB <-lubridate::as_date(data$DATE_ACC.CB)
# calculate intervals of service
data <- data %>% dplyr::mutate(LOS_DTS = lubridate::interval(lubridate::ymd(data$DATE_ACC.CB), lubridate::ymd(data$ADSVC_PE_DT)))
# create intervals by year
cohort_2000 <- lubridate::interval(lubridate::ymd("2000-01-01"), lubridate::ymd("2000-12-31"))
cohort_2001 <- lubridate::interval(lubridate::ymd("2001-01-01"), lubridate::ymd("2001-12-31"))
cohort_2002 <- lubridate::interval(lubridate::ymd("2002-01-01"), lubridate::ymd("2002-12-31"))
cohort_2003 <- lubridate::interval(lubridate::ymd("2003-01-01"), lubridate::ymd("2003-12-31"))
cohort_2004 <- lubridate::interval(lubridate::ymd("2004-01-01"), lubridate::ymd("2004-12-31"))
cohort_2005 <- lubridate::interval(lubridate::ymd("2005-01-01"), lubridate::ymd("2005-12-31"))
cohort_2006 <- lubridate::interval(lubridate::ymd("2006-01-01"), lubridate::ymd("2006-12-31"))
cohort_2007 <- lubridate::interval(lubridate::ymd("2007-01-01"), lubridate::ymd("2007-12-31"))
cohort_2008 <- lubridate::interval(lubridate::ymd("2008-01-01"), lubridate::ymd("2008-12-31"))
cohort_2009 <- lubridate::interval(lubridate::ymd("2009-01-01"), lubridate::ymd("2009-12-31"))
cohort_2010 <- lubridate::interval(lubridate::ymd("2010-01-01"), lubridate::ymd("2010-12-31"))
cohort_2011 <- lubridate::interval(lubridate::ymd("2011-01-01"), lubridate::ymd("2011-12-31"))
cohort_2012 <- lubridate::interval(lubridate::ymd("2012-01-01"), lubridate::ymd("2012-12-31"))
cohort_2013 <- lubridate::interval(lubridate::ymd("2013-01-01"), lubridate::ymd("2013-12-31"))
cohort_2014 <- lubridate::interval(lubridate::ymd("2014-01-01"), lubridate::ymd("2014-12-31"))
cohort_2015 <- lubridate::interval(lubridate::ymd("2015-01-01"), lubridate::ymd("2015-12-31"))
cohort_2016 <- lubridate::interval(lubridate::ymd("2016-01-01"), lubridate::ymd("2016-12-31"))
cohort_2017 <- lubridate::interval(lubridate::ymd("2017-01-01"), lubridate::ymd("2017-12-31"))
cohort_2018 <- lubridate::interval(lubridate::ymd("2018-01-01"), lubridate::ymd("2018-12-31"))
cohort_2019 <- lubridate::interval(lubridate::ymd("2019-01-01"), lubridate::ymd("2019-12-31"))
# calcuate whether intervals overlap with target cohort year; if TRUE, then that individual was active in that year
data$cohort.2000 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2000)
data$cohort.2001 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2001)
data$cohort.2002 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2002)
data$cohort.2003 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2003)
data$cohort.2004 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2004)
data$cohort.2005 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2005)
data$cohort.2006 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2006)
data$cohort.2007 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2007)
data$cohort.2008 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2008)
data$cohort.2009 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2009)
data$cohort.2010 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2010)
data$cohort.2011 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2011)
data$cohort.2012 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2012)
data$cohort.2013 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2013)
data$cohort.2014 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2014)
data$cohort.2015 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2015)
data$cohort.2016 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2016)
data$cohort.2017 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2017)
data$cohort.2018 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2018)
data$cohort.2019 <- lubridate::int_overlaps(data$LOS_DTS, cohort_2019)

## Alternative length of service variable using transaction date and transaction code (seems closer to reported numbers on enlisted and officers)
## TXN_EFF_DT missing: overall = 0.057, enlisted = 0.056, officer = 0.076
## ADP_TXN_TYP_CD missing: overall = 0.057, enlisted = 0.056, officer = 0.076
data$TXN_EFF_DT <-as.character(data$TXN_EFF_DT)
data$TXN_EFF_DT[is.na(data$TXN_EFF_DT)] <- ""
# Create new variable of attrition by recoding last transaction code to be remain or attrit
data <- data %>% dplyr::mutate(ATTRIT.CB = dplyr::recode(data$ADP_TXN_TYP_CD, "001" = "Remain", "002" = "Remain", "003" = "Remain", "004" = "Remain", "110" = "Remain", "111" = "Remain", 
                                                         "112" = "Remain", "115" = "Remain", "117" = "Remain", "118" = "Remain", "119" = "Remain", "120" = "Remain", "123" = "Remain", "130" = "Attrit", "131" = "Attrit", 
                                                         "132" = "Attrit", "135" = "Attrit", "137" = "Attrit", "138" = "Attrit", "139" = "Remain", "140" = "Attrit", "151" = "Remain", "152" = "Remain", "999" = "Remain"))
# Create new date varaible by using TXN_EFF_DT if the last code was attrit and use a date in the future to indicate that the Soldier is still in the Army
data$ATTRIT_DT.CB <- ifelse(data$ATTRIT.CB == "Attrit", data$TXN_EFF_DT, "2020-01-01")
data$TXN_EFF_DT[data$TXN_EFF_DT == ""] <- NA
# calculate intervals of service
data$DATE_ACC.CB <-lubridate::as_date(data$DATE_ACC.CB)
data$ATTRIT_DT.CB <-lubridate::as_date(data$ATTRIT_DT.CB)
data <- data %>% dplyr::mutate(LOS_DTS_2 = lubridate::interval(lubridate::ymd(data$DATE_ACC.CB), lubridate::ymd(data$ATTRIT_DT.CB)))
# create intervals by year
cohort_2000 <- lubridate::interval(lubridate::ymd("2000-01-01"), lubridate::ymd("2000-12-31"))
cohort_2001 <- lubridate::interval(lubridate::ymd("2001-01-01"), lubridate::ymd("2001-12-31"))
cohort_2002 <- lubridate::interval(lubridate::ymd("2002-01-01"), lubridate::ymd("2002-12-31"))
cohort_2003 <- lubridate::interval(lubridate::ymd("2003-01-01"), lubridate::ymd("2003-12-31"))
cohort_2004 <- lubridate::interval(lubridate::ymd("2004-01-01"), lubridate::ymd("2004-12-31"))
cohort_2005 <- lubridate::interval(lubridate::ymd("2005-01-01"), lubridate::ymd("2005-12-31"))
cohort_2006 <- lubridate::interval(lubridate::ymd("2006-01-01"), lubridate::ymd("2006-12-31"))
cohort_2007 <- lubridate::interval(lubridate::ymd("2007-01-01"), lubridate::ymd("2007-12-31"))
cohort_2008 <- lubridate::interval(lubridate::ymd("2008-01-01"), lubridate::ymd("2008-12-31"))
cohort_2009 <- lubridate::interval(lubridate::ymd("2009-01-01"), lubridate::ymd("2009-12-31"))
cohort_2010 <- lubridate::interval(lubridate::ymd("2010-01-01"), lubridate::ymd("2010-12-31"))
cohort_2011 <- lubridate::interval(lubridate::ymd("2011-01-01"), lubridate::ymd("2011-12-31"))
cohort_2012 <- lubridate::interval(lubridate::ymd("2012-01-01"), lubridate::ymd("2012-12-31"))
cohort_2013 <- lubridate::interval(lubridate::ymd("2013-01-01"), lubridate::ymd("2013-12-31"))
cohort_2014 <- lubridate::interval(lubridate::ymd("2014-01-01"), lubridate::ymd("2014-12-31"))
cohort_2015 <- lubridate::interval(lubridate::ymd("2015-01-01"), lubridate::ymd("2015-12-31"))
cohort_2016 <- lubridate::interval(lubridate::ymd("2016-01-01"), lubridate::ymd("2016-12-31"))
cohort_2017 <- lubridate::interval(lubridate::ymd("2017-01-01"), lubridate::ymd("2017-12-31"))
cohort_2018 <- lubridate::interval(lubridate::ymd("2018-01-01"), lubridate::ymd("2018-12-31"))
cohort_2019 <- lubridate::interval(lubridate::ymd("2019-01-01"), lubridate::ymd("2019-12-31"))
# calcuate whether intervals overlap with target cohort year; if TRUE, then that individual was active in that year
data$cohort.2000_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2000)
data$cohort.2001_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2001)
data$cohort.2002_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2002)
data$cohort.2003_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2003)
data$cohort.2004_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2004)
data$cohort.2005_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2005)
data$cohort.2006_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2006)
data$cohort.2007_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2007)
data$cohort.2008_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2008)
data$cohort.2009_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2009)
data$cohort.2010_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2010)
data$cohort.2011_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2011)
data$cohort.2012_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2012)
data$cohort.2013_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2013)
data$cohort.2014_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2014)
data$cohort.2015_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2015)
data$cohort.2016_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2016)
data$cohort.2017_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2017)
data$cohort.2018_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2018)
data$cohort.2019_2 <- lubridate::int_overlaps(data$LOS_DTS_2, cohort_2019)


## Create combined bad papers variable
data$badpaper.overall <- data %>% dplyr::select(COURT_MARTIAL, LETTER_REPRIMAND, ARTICLE15) %>% rowSums(na.rm = TRUE)
data$badpaper.overall <- as.integer(data$badpaper.overall)

## Create new variable of only 3-digit zip code
data <- data %>% dplyr::mutate(zipcode3 = substr(data$HOR_ZIPCODE.CB, 1, 3)) # only take first three digits of zipcode

## Create new race grouping [1 = Ameerican Indian/Alaskan Native, 2 = Asian, 3 = Black or African American, 4 = Native Hawaiian/Pasific Islander, 5 = White, 6 = Mixed Race, 7 = unkown]
data$RACE_CD <- as.character(data$RACE_CD)
data <- data %>% dplyr::mutate(RACE_CD_RE = dplyr::recode(data$RACE_CD, "1" = 1, "2" = 2, "3" = 3, "4" = 4, "5" = 5, "100" = 6, "101" = 6, "102" = 6,
                                                          "103" = 6, "104" = 6, "105" = 6, "106" = 6, "107" = 6, "108" = 6, "109" = 6, "110" = 6, "111" = 6, "112" = 6,
                                                          "113" = 6, "114" = 6, "115" = 6, "116" = 6, "117" = 6, "118" = 6, "119" = 6, "120" = 6, "121" = 6, "122" = 6,
                                                          "123" = 6, "124" = 6, "125" = 6, "999" = 7))

## Green to Gold
data <- data %>% dplyr::mutate(Green2Gold = case_when(RANK_PDE_GRP == "Enlisted" & RANK_PDE_GRP_last == "Officer" ~ "Y", 
                                                      TRUE ~ "N"))

#### Data labels -----------------------------------------------------------

# Faith group
data$FAITH_GRP.CB <- factor(data$FAITH_GRP.CB,
                            levels = c('1', '2', '3', '4', '5', '6', '7', '8', '9', '10'),
                            labels = c("no preference", "atheist", "agnostic", "christian", "jewish", "muslim", "hindu", "buddist", "sikh", "other"))

# Marital Status (at accession)
data$MRTL_STAT.CB <- factor(data$MRTL_STAT.CB,
                            levels = c('A', 'D', 'I', 'L', 'M', 'N', 'W', 'Z'),
                            labels = c("anulled", "divorced", "interlocutory decree", "legally seperated", "married", "never married", "widow(er)", "unknown"))

# Marital Status (last file date)
data$MRTL_STAT_CD_last <- factor(data$MRTL_STAT_CD_last,
                                 levels = c('A', 'D', 'I', 'L', 'M', 'N', 'W', 'Z'),
                                 labels = c("anulled", "divorced", "interlocutory decree", "legally seperated", "married", "never married", "widow(er)", "unknown"))

# Branch
data$SERVICE <- factor(data$SERVICE,
                       levels = c('A', 'F', 'C', 'M', 'N', 'X', 'Z'),
                       labels = c("Army", "Air Force", "Coast Guard", "Marines", "VY", "Civilian/GS", 
                                  "Other"))
# Service component
data$COMPO <- factor(data$COMPO,
                     levels = c('R', 'V', 'G', 'Z'),
                     labels = c("Active Duty", "Reserve", "Guard", "None"))

# Rank Grouping
data$RANK_PDE_GRP <- factor(data$RANK_PDE_GRP,
                            levels = c('Enlisted', 'Officer', 'Warrant Officer'),
                            labels = c("Enlisted", "Officer", "Warrant Officer"))

# Rank Grouping (last)
data$RANK_PDE_GRP_last <- factor(data$RANK_PDE_GRP_last,
                                 levels = c('Enlisted', 'Officer', 'Warrant Officer'),
                                 labels = c("Enlisted", "Officer", "Warrant Officer"))

# Race
data$RACE_CD_RE <- factor(data$RACE_CD_RE,
                          levels = c('1', '2', '3', '4', '5', '6', '7'),
                          labels = c("american indian/Alaskan native", "asian", "black", "native hawaiian/pacific islander", "white", "mixed race", "other"))
# Sex
data$PN_SEX_CD <- factor(data$PN_SEX_CD,
                         levels = c('M', 'F', 'Z'),
                         labels = c("male", "female", 'unknown')) 

# MOS Branch
data$MOS_BRANCH <- factor(data$MOS_BRANCH,
                          levels = c("AD", "AG", "AR", "AV", "CA", "CC", "CM", "EN", "FA", "FI", "HQ", "IN", "JA", "LC", "MD", "MI", "MP", "OD", "PO", "QM", "SC", "SF", "TC", "UN"),
                          labels = c("Air Defense", "Adjutant General", "Armor", "Aviation", "Civil Affairs", "Chaplain Corps", "Chemical", "Corps of Engineers", "Field Artillery", "Financial Management", 
                                     "Headquarters", "Infantry", "Judge Advocate General", "Logistics", "Medical", "Military Intelligence", "Military Police", "Ordinance", "Psychological Operations",
                                     "Quartermaster Corps", "Signal Corps", "Special Forces", "Transportation", "Unknown"))
# MOS Category
data$MOS_TYPE <- factor(data$MOS_TYPE,
                        levels = c('CA', 'CS', 'CSS', 'SPEC', 'OPS', 'UNK'),
                        labels = c("combat arms", "combat support", "combat service support", "special service", "operations", "unknown"))
# Prior Service
data$PS.CB <- factor(data$PS.CB,
                     levels = c('N', 'Y'),
                     labels = c("No", "Yes"))

# Education level (first)
data$EDU_LVL_CD <- factor(data$EDU_LVL_CD,
                          levels = c('11', '12', '13', '14', '21', '22', '23', '24', '25', '26', '27', '28', '31', '32', '41', '42', '43', '44',
                                     '45', '46', '51', '52', '61', '62', '63', '64', '65', '99'),
                          labels = c('less than H.S.', 'attending H.S., junior or less', 'attending H.S., senior', 'secondary school credential near completion',
                                     'test-based equivalency diploma', 'occupational program cert.', 'coorespondence school diploma', 'H.S. cert of attendance', 
                                     'home study diploma', 'adult education diploma', 'ARNG challenge program GED cert.', 'Other non-traditional H.S. credential',
                                     'H.S. diploma', 'completed H.S. (no diploma)', 'completed one semester of college, no H.S.', '1 yr of college cert of equivalency',
                                     '1-2 yrs college, no degree', 'associate degree', 'prof. nursing diploma', '3-4 yr college, no degree', 'baccalureate', 
                                     '1 or more yrs grad school, no degree', 'master degree', 'post master degree', 'first prof. degree', 'doctorate degree', 
                                     'post-doc degree', 'unknown'))
# Education level (last)
data$EDU_LVL_CD_last <- factor(data$EDU_LVL_CD_last,
                               levels = c('11', '12', '13', '14', '21', '22', '23', '24', '25', '26', '27', '28', '31', '32', '41', '42', '43', '44',
                                          '45', '46', '51', '52', '61', '62', '63', '64', '65', '99'),
                               labels = c('less than H.S.', 'attending H.S., junior or less', 'attending H.S., senior', 'secondary school credential near completion',
                                          'test-based equivalency diploma', 'occupational program cert.', 'coorespondence school diploma', 'H.S. cert of attendance', 
                                          'home study diploma', 'adult education diploma', 'ARNG challenge program GED cert.', 'Other non-traditional H.S. credential',
                                          'H.S. diploma', 'completed H.S. (no diploma)', 'completed one semester of college, no H.S.', '1 yr of college cert of equivalency',
                                          '1-2 yrs college, no degree', 'associate degree', 'prof. nursing diploma', '3-4 yr college, no degree', 'baccalureate', 
                                          '1 or more yrs grad school, no degree', 'master degree', 'post master degree', 'first prof. degree', 'doctorate degree', 
                                          'post-doc degree', 'unknown'))

# Education level reduced (first)
data$EDU_LVL_RE <- factor(data$EDU_LVL_RE,
                          levels = c('1', '2', '3', '4', '5', '6', '7', '8', '9'),
                          labels = c("less than H.S.", "H.S. & equivalent", "some college", "associate & prof. degree", "bachelor degree", "some grad", 
                                     "master degree", "doctorate degree", "unknown"))
# Education level reduced (last)
data$EDU_LVL_RE_last <- factor(data$EDU_LVL_RE_last,
                               levels = c('1', '2', '3', '4', '5', '6', '7', '8', '9'),
                               labels = c("less than H.S.", "H.S. & equivalent", "some college", "associate & prof. degree", "bachelor degree", "some grad", 
                                          "master degree", "doctorate degree", "unknown"))

# Discharge Type (Character of Service)
data$CHAR_SVC_CD <- factor(data$CHAR_SVC_CD,
                           levels = c('A', 'B', 'H', 'J', 'D', 'E', 'K', 'F', 'Y', 'Z'),
                           labels = c("honorable", "under honorable conditions (general)", "honorable (absence of a negative report)", "honorable for VA purposes", 
                                      "bad conduct", "under other than honorable", "dishonorable for VA purposes", "dishonorable", "uncharacterized", "unknown"))

# Discharge Type (Character of Service) reduced
data$CHAR_SVC_CD2 <- factor(data$CHAR_SVC_CD2,
                            levels = c('1', '0'),
                            labels = c("honorable", "dishonorable"))
# Reorganize
names(data)
head(data)
data <- data %>% dplyr::select(PID_PDE, DATE_BIRTH.CB, PN_SEX_CD, RACE_CD_RE, FAITH_GRP.CB, HOR_STATE.CB, zipcode3, HOR_ZIPCODE.CB, MRTL_STAT.CB, MRTL_STAT_CD_last, 
                               SERVICE, COMPO, RANK_PDE, RANK_PDE_last, RANK_PDE_GRP, RANK_PDE_GRP_last, Green2Gold, DTY_BASE_NAME.CB, PAYGRADE_PDE, PAYGRADE_PDE_last, PS.CB, 
                               MOS.CB, MOS_NAME, MOS_BRANCH, MOS_TYPE, AFQT_PCTL.CB, HEIGHT.CB, WEIGHT.CB, PULHES.P.CB, PULHES.U.CB, PULHES.L.CB, PULHES.H.CB, PULHES.E.CB, PULHES.S.CB, PULHES.TOTAL, PULHES.MEAN,
                               FILE_DT, FILE_DT_last, DATE_ACC.CB, YEAR_ACC.CB, LOS_DTS, LOS_DTS_2, AGE_ACC, EDU_LVL_CD, EDU_LVL_CD_last, EDU_LVL_RE, EDU_LVL_RE_last, award_count, COURT_MARTIAL, LETTER_REPRIMAND, ARTICLE15,  badpaper.overall, 
                               TXN_EFF_DT, CHAR_SVC_CD, CHAR_SVC_CD2, SEP_CD.CB, TRANS_TYPE.CB, TRANS_TYPE_RE.CB, ATTRIT.CB, ATTRIT_DT.CB, DATE_BIRTH_PDE, RACE_CD, FAITH_GRP_CD, MRTL_STAT_CD, HOR_US_ST_CD, PN_MA_US_ST_CNTY_CD, ZIP_CODE_PDE_PN_MA, AFQT_PCTL_SCR_QY.x,  
                               PRI_SVC_OCC_CD, DTY_BASE_FAC_ID, ASG_BASE_FAC_ID, DATE_BIRTH.x, RELIGION, MARITAL, HEIGHT, WEIGHT, PULHES, STATE, CITY, ZIP_CODE_PDE, AFQT, DATE_ACC, AFMS_BASE_DT, USVC_INIT_ENT_DT, CAR_DIV, MOS, PS, SNPSHT_DT, DATE_BIRTH.y, 
                               PN_FAITH_GRP_CD, PN_MA_US_ST_CD, PN_MA_CTY_NM, PN_MRTL_STAT_CD, HGT_DM, PN_WGHT_QY, PHY_CPCY_PHY_PRFL_MOD_CD, UXTR_PHY_PRFL_MOD_CD, LXTR_PHY_PRFL_MOD_CD, HRG_PHY_PRFL_MOD_CD, VSN_PHY_PRFL_MOD_CD, PSYC_PHY_PRFL_MOD_CD, 
                               AFQT_PCTL_SCR_QY.y, APLNT_USVC_AGMT_APP_DT, ACC_PRI_SVC_OCC_CD, MEP_PRIOR_SVC_IND_CD, ADSVC_PE_DT, ENL_ASVC_OBLG_END_DT, ADP_TXN_TYP_CD, ISVC_SEP_CD, FAITH_GRP_CD.R, PN_FAITH_GRP_CD.R, 
                               PULHES.P, PULHES.U, PULHES.L, PULHES.H, PULHES.E, PULHES.S, everything())
length(unique(data$PID_PDE))
# Retain only unique PIDs
data <- data %>% dplyr::distinct(PID_PDE, .keep_all = TRUE)

data.table::fwrite(data, file = "/Army20Yr_linked_data_analytics.csv", row.names = F) # save recoded and new variable file


#### Data Analysis across 20 years of the Army -----------------------------------------------------------


#### Frequencies ====================================================================================

## Overall time frame (2000-2019)

# Soldier branch (Army, AF, Navy, CG, Marines)
f_O_1 <- tibble::rownames_to_column(questionr::freq(data$SERVICE, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Branch") %>% dplyr::select(var, everything())
# Soldier component (Active, Reserve, Guard)
f_O_2 <- tibble::rownames_to_column(questionr::freq(data$COMPO, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Compo") %>% dplyr::select(var, everything())
# Soldier rank (start)
f_O_3 <- tibble::rownames_to_column(questionr::freq(data$RANK_PDE, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Rank (Start)") %>% dplyr::select(var, everything())
# Soldier rank (end)
f_O_4 <- tibble::rownames_to_column(questionr::freq(data$RANK_PDE_last, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Rank (End)") %>% dplyr::select(var, everything())
# Soldier rank group (start)
f_O_5 <- tibble::rownames_to_column(questionr::freq(data$RANK_PDE_GRP, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Rank Group (Start)") %>% dplyr::select(var, everything())
# Soldier rank group (end)
f_O_6 <- tibble::rownames_to_column(questionr::freq(data$RANK_PDE_GRP_last, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Rank Group (End)") %>% dplyr::select(var, everything())
# Soldier green to gold
f_O_7 <- tibble::rownames_to_column(questionr::freq(data$Green2Gold, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Enlisted to Officer") %>% dplyr::select(var, everything())
# Soldier MOS name
f_O_8 <- tibble::rownames_to_column(questionr::freq(data$MOS_NAME, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "MOS Name") %>% dplyr::select(var, everything())
# Soldier MOS Branch
f_O_9 <- tibble::rownames_to_column(questionr::freq(data$MOS_BRANCH, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "MOS Branch") %>% dplyr::select(var, everything())
# Soldier MOS Type
f_O_10 <- tibble::rownames_to_column(questionr::freq(data$MOS_TYPE, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "MOS Type") %>% dplyr::select(var, everything())
# Soldier prior service
f_O_11 <- tibble::rownames_to_column(questionr::freq(data$PS.CB, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Prior Service") %>% dplyr::select(var, everything())
# Soldier year accession
f_O_12 <- tibble::rownames_to_column(questionr::freq(data$YEAR_ACC.CB, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Accession Year") %>% dplyr::select(var, everything())
# Type of discharge
f_O_13 <- tibble::rownames_to_column(questionr::freq(data$CHAR_SVC_CD, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Discharge Type") %>% dplyr::select(var, everything())
# Type of discharge2
f_O_14 <- tibble::rownames_to_column(questionr::freq(data$CHAR_SVC_CD2, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Discharge Type (Redux)") %>% dplyr::select(var, everything())
# Court Martial Count
f_O_15 <- tibble::rownames_to_column(questionr::freq(data$COURT_MARTIAL, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Court Martial") %>% dplyr::select(var, everything())
# Letter of Reprimand Count
f_O_16 <- tibble::rownames_to_column(questionr::freq(data$LETTER_REPRIMAND, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Letter of Reprimand") %>% dplyr::select(var, everything())
# Article 15 Count
f_O_17 <- tibble::rownames_to_column(questionr::freq(data$ARTICLE15, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Article 15") %>% dplyr::select(var, everything())
# Bad Papers Overall (combined count of CM, LoR, A15)
f_O_18 <- tibble::rownames_to_column(questionr::freq(data$badpaper.overall, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Overall Bad Papers") %>% dplyr::select(var, everything())
# Soldier age at accession
f_O_19 <- tibble::rownames_to_column(questionr::freq(as.integer(data$AGE_ACC), digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Age at Accession") %>% dplyr::select(var, everything())
# Soldier sex at accession
f_O_20 <- tibble::rownames_to_column(questionr::freq(data$PN_SEX_CD, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Soldier Sex") %>% dplyr::select(var, everything())
# Soldier race at accession
f_O_21 <- tibble::rownames_to_column(questionr::freq(data$RACE_CD_RE, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Soldier Race") %>% dplyr::select(var, everything())
# Soldier highest level education (start)
f_O_22 <- tibble::rownames_to_column(questionr::freq(data$EDU_LVL_CD, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (Start)") %>% dplyr::select(var, everything())
# Soldier highest level education (end)
f_O_23 <- tibble::rownames_to_column(questionr::freq(data$EDU_LVL_CD_last, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (End)") %>% dplyr::select(var, everything())
# Soldier highest level education (redux-start)
f_O_24 <- tibble::rownames_to_column(questionr::freq(data$EDU_LVL_RE, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (Redux-Start)") %>% dplyr::select(var, everything())
# Soldier highest level education (redux-end)
f_O_25 <- tibble::rownames_to_column(questionr::freq(data$EDU_LVL_RE_last, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Education (Redux-End)") %>% dplyr::select(var, everything())
# Soldier marital status (start)
f_O_26 <- tibble::rownames_to_column(questionr::freq(data$MRTL_STAT.CB, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Marital Status (Start)") %>% dplyr::select(var, everything())
# Soldier marital status (end)
f_O_27 <- tibble::rownames_to_column(questionr::freq(data$MRTL_STAT_CD_last, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Marital Status (end)") %>% dplyr::select(var, everything())
# Faith group
f_O_28 <- tibble::rownames_to_column(questionr::freq(data$FAITH_GRP.CB, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Faith Group") %>% dplyr::select(var, everything())
# First duty location
f_O_29 <- tibble::rownames_to_column(questionr::freq(data$DTY_BASE_NAME.CB, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "First Duty Location") %>% dplyr::select(var, everything())
# Seperation Code
f_O_30 <- tibble::rownames_to_column(questionr::freq(data$SEP_CD.CB, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Seperation Code") %>% dplyr::select(var, everything())
# Last Transaction Code
f_O_31 <- tibble::rownames_to_column(questionr::freq(data$TRANS_TYPE.CB, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Last Transaction Code") %>% dplyr::select(var, everything())
# HQ Recruits
f_O_32 <- tibble::rownames_to_column(questionr::freq(data$HQ_RECRUIT, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "High Quality Recruits") %>% dplyr::select(var, everything())
# SES
f_O_33 <- tibble::rownames_to_column(questionr::freq(data$TFSES_HOLLHEAD, digits = 4, cum = TRUE, sort = "dec", total = TRUE, na.last = TRUE)) %>% mutate(var = "Hollingshead 2 Factor SES") %>% dplyr::select(var, everything())

freq_O_c <- rbind(f_O_1, f_O_2, f_O_3, f_O_4, f_O_5, f_O_6,f_O_7, f_O_8, f_O_9, f_O_10, f_O_11, f_O_12, f_O_13, f_O_14, f_O_15, f_O_16, f_O_17, 
                  f_O_18, f_O_19, f_O_20, f_O_21, f_O_22, f_O_23, f_O_24, f_O_25, f_O_26, f_O_27, f_O_28, f_O_29, f_O_30, f_O_31, f_O_32, f_O_33)
write.csv(freq_O_c, "Army20Yr_overall_freq.csv")


#### Descriptives ====================================================================================

# Overall descriptives (2000-2016)
desc_O_c <- desc.yr(data)
write.csv(desc_O_c,  "Army20Yr_ENLOFF_desc.csv") # save output

# Create filter variables for each accession year
data2000 <- data %>% dplyr::filter(YEAR_ACC.CB == '2000')
data2001 <- data %>% dplyr::filter(YEAR_ACC.CB == '2001')
data2002 <- data %>% dplyr::filter(YEAR_ACC.CB == '2002')
data2003 <- data %>% dplyr::filter(YEAR_ACC.CB == '2003')
data2004 <- data %>% dplyr::filter(YEAR_ACC.CB == '2004')
data2005 <- data %>% dplyr::filter(YEAR_ACC.CB == '2005')
data2006 <- data %>% dplyr::filter(YEAR_ACC.CB == '2006')
data2007 <- data %>% dplyr::filter(YEAR_ACC.CB == '2007')
data2008 <- data %>% dplyr::filter(YEAR_ACC.CB == '2008')
data2009 <- data %>% dplyr::filter(YEAR_ACC.CB == '2009')
data2010 <- data %>% dplyr::filter(YEAR_ACC.CB == '2010')
data2011 <- data %>% dplyr::filter(YEAR_ACC.CB == '2011')
data2012 <- data %>% dplyr::filter(YEAR_ACC.CB == '2012')
data2013 <- data %>% dplyr::filter(YEAR_ACC.CB == '2013')
data2014 <- data %>% dplyr::filter(YEAR_ACC.CB == '2014')
data2015 <- data %>% dplyr::filter(YEAR_ACC.CB == '2015')
data2016 <- data %>% dplyr::filter(YEAR_ACC.CB == '2016')
data2017 <- data %>% dplyr::filter(YEAR_ACC.CB == '2017')
data2018 <- data %>% dplyr::filter(YEAR_ACC.CB == '2018')
data2019 <- data %>% dplyr::filter(YEAR_ACC.CB == '2019')


# Descriptives by year of accession
desc.2000 <- desc.yr(x = data2000) %>% dplyr::mutate(ACC_YEAR = "2000") %>% dplyr::select(ACC_YEAR, everything())
desc.2001 <- desc.yr(x = data2001) %>% dplyr::mutate(ACC_YEAR = "2001") %>% dplyr::select(ACC_YEAR, everything())
desc.2002 <- desc.yr(x = data2002) %>% dplyr::mutate(ACC_YEAR = "2002") %>% dplyr::select(ACC_YEAR, everything())
desc.2003 <- desc.yr(x = data2003) %>% dplyr::mutate(ACC_YEAR = "2003") %>% dplyr::select(ACC_YEAR, everything())
desc.2004 <- desc.yr(x = data2004) %>% dplyr::mutate(ACC_YEAR = "2004") %>% dplyr::select(ACC_YEAR, everything())
desc.2005 <- desc.yr(x = data2005) %>% dplyr::mutate(ACC_YEAR = "2005") %>% dplyr::select(ACC_YEAR, everything())
desc.2006 <- desc.yr(x = data2006) %>% dplyr::mutate(ACC_YEAR = "2006") %>% dplyr::select(ACC_YEAR, everything())
desc.2007 <- desc.yr(x = data2007) %>% dplyr::mutate(ACC_YEAR = "2007") %>% dplyr::select(ACC_YEAR, everything())
desc.2008 <- desc.yr(x = data2008) %>% dplyr::mutate(ACC_YEAR = "2008") %>% dplyr::select(ACC_YEAR, everything())
desc.2009 <- desc.yr(x = data2009) %>% dplyr::mutate(ACC_YEAR = "2009") %>% dplyr::select(ACC_YEAR, everything())
desc.2010 <- desc.yr(x = data2010) %>% dplyr::mutate(ACC_YEAR = "2010") %>% dplyr::select(ACC_YEAR, everything())
desc.2011 <- desc.yr(x = data2011) %>% dplyr::mutate(ACC_YEAR = "2011") %>% dplyr::select(ACC_YEAR, everything())
desc.2012 <- desc.yr(x = data2012) %>% dplyr::mutate(ACC_YEAR = "2012") %>% dplyr::select(ACC_YEAR, everything())
desc.2013 <- desc.yr(x = data2013) %>% dplyr::mutate(ACC_YEAR = "2013") %>% dplyr::select(ACC_YEAR, everything())
desc.2014 <- desc.yr(x = data2014) %>% dplyr::mutate(ACC_YEAR = "2014") %>% dplyr::select(ACC_YEAR, everything())
desc.2015 <- desc.yr(x = data2015) %>% dplyr::mutate(ACC_YEAR = "2015") %>% dplyr::select(ACC_YEAR, everything())
desc.2016 <- desc.yr(x = data2016) %>% dplyr::mutate(ACC_YEAR = "2016") %>% dplyr::select(ACC_YEAR, everything())
desc.2017 <- desc.yr(x = data2017) %>% dplyr::mutate(ACC_YEAR = "2017") %>% dplyr::select(ACC_YEAR, everything())
desc.2018 <- desc.yr(x = data2018) %>% dplyr::mutate(ACC_YEAR = "2018") %>% dplyr::select(ACC_YEAR, everything())
desc.2019 <- desc.yr(x = data2019) %>% dplyr::mutate(ACC_YEAR = "2019") %>% dplyr::select(ACC_YEAR, everything())

desc_Yr_c <- rbind(desc.2000, desc.2001, desc.2002, desc.2003, desc.2004, desc.2005, desc.2006, desc.2007, desc.2008, desc.2009, desc.2010,
                   desc.2011, desc.2012, desc.2013, desc.2014, desc.2015, desc.2016, desc.2017, desc.2018, desc.2019)

#### Obtain crosstab values ----------------------------------------------------------------------
ct1 <- data %>% dplyr::group_by(YEAR_ACC.CB, zipcode3) %>% dplyr::summarise(n = n())
write.csv(ct1, "Army20Yr_YearACCbyZip3_crosstabs.csv")

ct2 <- data %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB, zipcode3) %>% dplyr::summarise(n = n())
write.csv(ct2, "Army20Yr_RANKGRPbyYEARACCbyZIP3_crosstabs.csv")

ct3 <- data %>% dplyr::group_by(YEAR_ACC.CB, HOR_STATE.CB) %>% dplyr::summarise(n = n())
write.csv(ct3, "Army20Yr_YEARACCbySTATE_crosstabs.csv")

names(data)
data$MEPSTATE <- as.character(data$MEPSTATE)
data$STATE <- as.character(data$STATE)
data$MASTSTATE <- as.character(data$MASTSTATE)
data$MEPSTATE.CB <- dplyr::coalesce(data$MEPSTATE, data$STATE, data$MASTSTATE)
data$MEPSTATE.CB <- as.character(data$MEPSTATE.CB)
data$MEPSTATE.CB[data$MEPSTATE.CB == ""] <- NA
data$MEPSTATE.CB <- factor(data$MEPSTATE.CB)
sum(is.na(data$MEPSTATE.CB))/length(data$PID_PDE)*100 # 0.25%
ct3b <- data %>% dplyr::group_by(YEAR_ACC.CB, MEPSTATE.CB) %>% dplyr::summarise(n = n())
write.csv(ct3b, "Army20Yr_YEARACCbyMEPSTATE_crosstabs.csv")

ct4 <- data %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB, HOR_STATE.CB) %>% dplyr::summarise(n = n())
write.csv(ct4, "Army20Yr_RANKGRPbyYEARACCbySTATE_crosstabs.csv")


# if attrit year is 2020 it means no attrition has occured
data %>% dplyr::select(ATTRIT_YEAR.CB, TXN_EFF_DT)
data$ATTRIT_DT.CB <- lubridate::as_date(data$ATTRIT_DT.CB)
data$ATTRIT_YEAR.CB <- format(data$ATTRIT_DT.CB, "%Y")
ct5 <- data %>% dplyr::group_by(RANK_PDE_GRP, ATTRIT_YEAR.CB, SEP_CD.CB) %>% dplyr::summarise(n = n())
write.csv(ct5, "Army20Yr_RANKGRPbyATTRITYRbySEPCD_crosstabs.csv")


ct6 <- data %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB, MRTL_STAT.CB) %>% dplyr::summarise(n = n())
write.csv(ct6, "Army20Yr_RANKGRPbyYEARACCbyMARRIED_crosstabs.csv")

ct7 <- data %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB, EDU_LVL_CD) %>% dplyr::summarise(n = n())
write.csv(ct7, "Army20Yr_RANKGRPbyYEARACCbyEDU_crosstabs.csv")


# crosstab of BMI
data$BMI <- ((data$WEIGHT.CB * 703) / ((data$HEIGHT.CB)^2))
data %>% dplyr::select(PID_PDE, WEIGHT.CB, HEIGHT.CB, BMI)

bmi.up <- data %>% select(PID_PDE, YEAR_ACC.CB, RANK_PDE_GRP, HEIGHT.CB, WEIGHT.CB, BMI) %>% dplyr::arrange(desc(BMI))
bmi.dn <- data %>% select(PID_PDE, YEAR_ACC.CB, RANK_PDE_GRP, HEIGHT.CB, WEIGHT.CB, BMI) %>% dplyr::arrange(BMI)
mean(data$BMI, na.rm = TRUE) # 24.87, -3 SDs = 0, +3 SDs = 58.81
sd(data$BMI, na.rm = TRUE) # 11.31, 3 SDs = 33.94
IQR(data$BMI, na.rm = TRUE) # 5.23684
quantile(data$BMI, na.rm = TRUE) # Tukey Fence: first = 21.9687, third = 27.205589, 3xIQR = 15.71, lower cut off = 6.26, upper cut off = 42.92
#bmi.filt <- bmi %>% dplyr::filter(BMI < 42.92, BMI > 6.26)
sum(is.na(data$BMI)) # n = 109,326

ct8 <- data %>% dplyr::filter(BMI < 42.92, BMI > 6.26) %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::summarise(BMI_MEAN = mean(BMI, na.rm = TRUE), BMI_SD = sd(BMI, na.rm = TRUE), n = sum(!is.na(BMI)))
ct8 <- ct8 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BMI_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BMI_MEAN - MOE, CI.UPPER = BMI_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct8, "Army20Yr_YEARACCbyBMI_crosstabs.csv")

ct9 <- data %>% dplyr::filter(BMI < 42.92, BMI > 6.26) %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB) %>% dplyr::summarise(BMI_MEAN = mean(BMI, na.rm = TRUE), BMI_SD = sd(BMI, na.rm = TRUE), n = sum(!is.na(BMI)))
ct9 <- ct9 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BMI_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BMI_MEAN - MOE, CI.UPPER = BMI_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct9, "Army20Yr_RANKGRPbyYEARACCbyBMI_crosstabs.csv")

ct10 <- data %>% dplyr::filter(BMI < 42.92, BMI > 6.26) %>% dplyr::filter(PN_SEX_CD == "male" | PN_SEX_CD == "female") %>% dplyr::group_by(PN_SEX_CD, YEAR_ACC.CB) %>% dplyr::summarise(BMI_MEAN = mean(BMI, na.rm = TRUE), BMI_SD = sd(BMI, na.rm = TRUE), n = sum(!is.na(BMI)))
ct10 <- ct10 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BMI_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BMI_MEAN - MOE, CI.UPPER = BMI_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct10, "Army20Yr_SEXbyYEARACCbyBMI_crosstabs.csv")


data$RACE.CT <- dplyr::recode(data$RACE_CD_RE, "white" = "White", "asian" = "Asian", "black" = "Black", "american indian/Alaskan native" = "American Indian/Alaskan Native", 
                              "native hawaiian/pacific islander" = "Native Hawaiian/Pacific Islander", "mixed race" = "Mixed Race/Other", "other" = "Mixed Race/Other")

ct10b <- data %>% dplyr::filter(BMI < 42.92, BMI > 6.26) %>% dplyr::group_by(YEAR_ACC.CB, RACE.CT) %>% dplyr::summarise(BMI_MEAN = mean(BMI, na.rm = TRUE), BMI_SD = sd(BMI, na.rm = TRUE), n = sum(!is.na(BMI)))
ct10b <- ct10b %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BMI_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BMI_MEAN - MOE, CI.UPPER = BMI_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct10b, "Army20Yr_YEARACCbyRACEbyBMI_crosstabs.csv")


# crosstab of first APFT score
ct11 <- data %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::summarise(APFT_MEAN = mean(APFT_1stSCORE, na.rm = TRUE), APFT_SD = sd(APFT_1stSCORE, na.rm = TRUE), n = sum(!is.na(APFT_1stSCORE)))
ct11 <- ct11 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(APFT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = APFT_MEAN - MOE, CI.UPPER = APFT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct11, "Army20Yr_YEARACCbyAPFT1_crosstabs.csv")

ct12 <- data %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB) %>% dplyr::summarise(APFT_MEAN = mean(APFT_1stSCORE, na.rm = TRUE), APFT_SD = sd(APFT_1stSCORE, na.rm = TRUE), n = sum(!is.na(APFT_1stSCORE)))
ct12 <- ct12 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(APFT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = APFT_MEAN - MOE, CI.UPPER = APFT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct12, "Army20Yr_RANKGRPbyYEARACCbyAPFT1_crosstabs.csv")

ct13 <- data %>% dplyr::group_by(PN_SEX_CD, YEAR_ACC.CB) %>% dplyr::summarise(APFT_MEAN = mean(APFT_1stSCORE, na.rm = TRUE), APFT_SD = sd(APFT_1stSCORE, na.rm = TRUE), n = sum(!is.na(APFT_1stSCORE)))
ct13 <- ct13 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(APFT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = APFT_MEAN - MOE, CI.UPPER = APFT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct13, "Army20Yr_SEXbyYEARACCbyAPFT1_crosstabs.csv")

levels(data$RACE_CD_RE)
data$RACE.CT <- dplyr::recode(data$RACE_CD_RE, "white" = "White", "asian" = "Asian", "black" = "Black", "american indian/Alaskan native" = "American Indian/Alaskan Native", 
                              "native hawaiian/pacific islander" = "Native Hawaiian/Pacific Islander", "mixed race" = "Mixed Race/Other", "other" = "Mixed Race/Other")
levels(data$RACE.CT)
ct13b <- data %>% dplyr::group_by(YEAR_ACC.CB, RACE.CT) %>% dplyr::summarise(APFT_MEAN = mean(APFT_1stSCORE, na.rm = TRUE), APFT_SD = sd(APFT_1stSCORE, na.rm = TRUE), n = sum(!is.na(APFT_1stSCORE)))
ct13b <- ct13b %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(APFT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = APFT_MEAN - MOE, CI.UPPER = APFT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct13b, "Army20Yr_YEARACCbyRACEbyAPFT1_crosstabs.csv")


# crosstab of Soldier sex
ct14 <- data %>% dplyr::filter(PN_SEX_CD == "male" | PN_SEX_CD == "female") %>% dplyr::group_by(YEAR_ACC.CB, PN_SEX_CD) %>% dplyr::summarise(n = n())
ct14 <- ct14 %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::mutate(countT = sum(n)) %>% dplyr::group_by(PN_SEX_CD, add = TRUE) %>% dplyr::mutate(pct = (n/countT)*100) %>% dplyr::select(-countT)
write.csv(ct14, "Army20Yr_YEARACCbyPN_SEX_CD_crosstabs.csv")

ct15 <- data %>% dplyr::filter(PN_SEX_CD == "male" | PN_SEX_CD == "female") %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB, PN_SEX_CD) %>% dplyr::summarise(n = n()) %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB) %>% 
  dplyr::mutate(pct = n/sum(n)*100)
write.csv(ct15, "Army20Yr_RANKGRPbyYEARACCbyPN_SEX_CD_crosstabs.csv")

# crosstab by Soldier race

ct16 <- data %>% dplyr::group_by(YEAR_ACC.CB, RACE_CD_RE) %>% dplyr::summarise(n = n())
ct16 <- ct16 %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::mutate(countT = sum(n)) %>% dplyr::group_by(RACE_CD_RE, add = TRUE) %>% dplyr::mutate(pct = (n/countT)*100) %>% dplyr::select(-countT)
write.csv(ct16, "Army20Yr_YEARACCbyRACE_crosstabs.csv")

ct17 <- data %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB, RACE_CD_RE) %>% dplyr::summarise(n = n()) %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB) %>% 
  dplyr::mutate(pct = n/sum(n)*100)
write.csv(ct17, "Army20Yr_RANKGRPbyYEARACCbyRACE_crosstabs.csv")


# raw counts
ct18 <- data %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB) %>% dplyr::summarise(n = n())
write.csv(ct18, "Army20Yr_RANKGRPbyYEARACC_crosstabs.csv")


# crosstab of AFQT score
ct19 <- data %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::summarise(AFQT_MEAN = mean(AFQT_PCTL.CB, na.rm = TRUE), AFQT_SD = sd(AFQT_PCTL.CB, na.rm = TRUE), n = sum(!is.na(AFQT_PCTL.CB)))
ct19 <- ct19 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AFQT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AFQT_MEAN - MOE, CI.UPPER = AFQT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct19, "Army20Yr_YEARACCbyAFQT_crosstabs.csv")

ct20 <- data %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB) %>% dplyr::summarise(AFQT_MEAN = mean(AFQT_PCTL.CB, na.rm = TRUE), AFQT_SD = sd(AFQT_PCTL.CB, na.rm = TRUE), n = sum(!is.na(AFQT_PCTL.CB)))
ct20 <- ct20 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AFQT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AFQT_MEAN - MOE, CI.UPPER = AFQT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct20, "Army20Yr_RANKGRPbyYEARACCbyAFQT_crosstabs.csv")

ct21 <- data %>% dplyr::filter(PN_SEX_CD == "male" | PN_SEX_CD == "female") %>% dplyr::group_by(PN_SEX_CD, YEAR_ACC.CB) %>% dplyr::summarise(AFQT_MEAN = mean(AFQT_PCTL.CB, na.rm = TRUE), AFQT_SD = sd(AFQT_PCTL.CB, na.rm = TRUE), n = sum(!is.na(AFQT_PCTL.CB)))
ct21 <- ct21 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AFQT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AFQT_MEAN - MOE, CI.UPPER = AFQT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct21, "Army20Yr_SEXbyYEARACCbyAFQT_crosstabs.csv")

ct22 <- data %>% dplyr::group_by(RACE_CD_RE, YEAR_ACC.CB) %>% dplyr::summarise(AFQT_MEAN = mean(AFQT_PCTL.CB, na.rm = TRUE), AFQT_SD = sd(AFQT_PCTL.CB, na.rm = TRUE), n = sum(!is.na(AFQT_PCTL.CB)))
ct22 <- ct22 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AFQT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AFQT_MEAN - MOE, CI.UPPER = AFQT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct22, "Army20Yr_RACEbyYEARACCbyAFQT_crosstabs.csv")


ct23 <- data %>% dplyr::group_by(RANK_PDE_GRP, EDU_LVL_CD, YEAR_ACC.CB) %>% dplyr::summarise(AFQT_MEAN = mean(AFQT_PCTL.CB, na.rm = TRUE), AFQT_SD = sd(AFQT_PCTL.CB, na.rm = TRUE), n = sum(!is.na(AFQT_PCTL.CB)))
ct23 <- ct23 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AFQT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AFQT_MEAN - MOE, CI.UPPER = AFQT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct23, "Army20Yr_RANKGRPbyEDULVLbyYEARACCbyAFQT_crosstabs.csv")


ct24 <- data %>% dplyr::group_by(HOR_STATE.CB, YEAR_ACC.CB) %>% dplyr::summarise(BMI_MEAN = mean(BMI, na.rm = TRUE), BMI_SD = sd(BMI, na.rm = TRUE), n = sum(!is.na(BMI)))
ct24 <- ct24 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BMI_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BMI_MEAN - MOE, CI.UPPER = BMI_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct24, "Army20Yr_STATEbyYEARACCbyBMI_crosstabs.csv")


ct25 <- data %>% dplyr::group_by(HOR_STATE.CB) %>% dplyr::summarise(BMI_MEAN = mean(BMI, na.rm = TRUE), BMI_SD = sd(BMI, na.rm = TRUE), n = sum(!is.na(BMI)))
ct25 <- ct25 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BMI_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BMI_MEAN - MOE, CI.UPPER = BMI_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct25, "Army20Yr_STATEbyBMI_crosstabs.csv")


ct26 <- data %>% dplyr::group_by(zipcode3) %>% dplyr::summarise(BMI_MEAN = mean(BMI, na.rm = TRUE), BMI_SD = sd(BMI, na.rm = TRUE), n = sum(!is.na(BMI)))
ct26 <- ct26 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BMI_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BMI_MEAN - MOE, CI.UPPER = BMI_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct26, "Army20Yr_ZIP3byBMI_crosstabs.csv")




ct27 <- data %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::summarise(n = n())
write.csv(ct27, "Army20Yr_YEARACC_crosstabs.csv")


ct28 <- data %>% dplyr::group_by(RANK_PDE_GRP, YEAR_ACC.CB) %>% dplyr::summarise(AGE.ACC_MEAN = mean(AGE_ACC, na.rm = TRUE), AGE.ACC_SD = sd(AGE_ACC, na.rm = TRUE), n = sum(!is.na(AGE_ACC)))
ct28 <- ct28 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AGE.ACC_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AGE.ACC_MEAN - MOE, CI.UPPER = AGE.ACC_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct28, "Army20Yr_RANKGRPbyYEARACCbyAGEACC_crosstabs.csv")


ct29 <- data %>% dplyr::group_by(YEAR_ACC.CB, HOR_ZIPCODE.CB) %>% dplyr::summarise(n = n())
write.csv(ct29, "Army20Yr_YearACCbyZIP5_crosstabs.csv")


ct30 <- data %>% dplyr::group_by(PN_SEX_CD, EDU_LVL_CD, YEAR_ACC.CB) %>% dplyr::summarise(AFQT_MEAN = mean(AFQT_PCTL.CB, na.rm = TRUE), AFQT_SD = sd(AFQT_PCTL.CB, na.rm = TRUE), n = sum(!is.na(AFQT_PCTL.CB)))
ct30 <- ct30 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AFQT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AFQT_MEAN - MOE, CI.UPPER = AFQT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct30, "Army20Yr_SEXbyEDULVLbyYEARACCbyAFQT_crosstabs.csv")


ct31 <- data %>% dplyr::group_by(YEAR_ACC.CB, MOS_TYPE) %>% dplyr::summarise(n = n())
write.csv(ct31, "Army20Yr_YEARACCbyMOSTYPE_crosstabs.csv")


ct32 <- data %>% dplyr::group_by(YEAR_ACC.CB, MOS_BRANCH) %>% dplyr::summarise(n = n())
write.csv(ct32, "Army20Yr_YEARACCbyMOSBRANCH_crosstabs.csv")


ct33 <- data %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::summarise(AWARD_MEAN = mean(award_count, na.rm = TRUE), AWARD_SD = sd(award_count, na.rm = TRUE), n = sum(!is.na(award_count)))
ct33 <- ct33 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AWARD_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AWARD_MEAN - MOE, CI.UPPER = AWARD_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct33, "Army20Yr_YEARACCbyAWARD_crosstabs.csv")


ct34 <- data %>% dplyr::group_by(YEAR_ACC.CB, RANK_PDE_GRP) %>% dplyr::summarise(AWARD_MEAN = mean(award_count, na.rm = TRUE), AWARD_SD = sd(award_count, na.rm = TRUE), n = sum(!is.na(award_count)))
ct34 <- ct34 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AWARD_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AWARD_MEAN - MOE, CI.UPPER = AWARD_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct34, "Army20Yr_YEARACCbyRANKGRPbyAWARD_crosstabs.csv")

ct35 <- data %>% dplyr::filter(PN_SEX_CD == "male" | PN_SEX_CD == "female") %>% dplyr::group_by(YEAR_ACC.CB, PN_SEX_CD) %>% dplyr::summarise(AWARD_MEAN = mean(award_count, na.rm = TRUE), AWARD_SD = sd(award_count, na.rm = TRUE), n = sum(!is.na(award_count)))
ct35 <- ct35 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AWARD_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AWARD_MEAN - MOE, CI.UPPER = AWARD_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct35, "Army20Yr_YEARACCbySEXbyAWARD_crosstabs.csv")

ct36 <- data %>% dplyr::group_by(YEAR_ACC.CB, RACE_CD_RE) %>% dplyr::summarise(AWARD_MEAN = mean(award_count, na.rm = TRUE), AWARD_SD = sd(award_count, na.rm = TRUE), n = sum(!is.na(award_count)))
ct36 <- ct36 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(AWARD_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = AWARD_MEAN - MOE, CI.UPPER = AWARD_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct36, "Army20Yr_YEARACCbyRACEbyAWARD_crosstabs.csv")



ct37 <- data %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::summarise(BADPAPER_MEAN = mean(badpaper.overall, na.rm = TRUE), BADPAPER_SD = sd(badpaper.overall, na.rm = TRUE), n = sum(!is.na(badpaper.overall)))
ct37 <- ct37 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BADPAPER_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BADPAPER_MEAN - MOE, CI.UPPER = BADPAPER_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct37, "Army20Yr_YEARACCbyBADPAPER_crosstabs.csv")

ct38 <- data %>% dplyr::group_by(YEAR_ACC.CB, RANK_PDE_GRP) %>% dplyr::summarise(BADPAPER_MEAN = mean(badpaper.overall, na.rm = TRUE), BADPAPER_SD = sd(badpaper.overall, na.rm = TRUE), n = sum(!is.na(badpaper.overall)))
ct38 <- ct38 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BADPAPER_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BADPAPER_MEAN - MOE, CI.UPPER = BADPAPER_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct38, "Army20Yr_YEARACCbyRANKGRPbyBADPAPER_crosstabs.csv")

ct39 <- data %>% dplyr::filter(PN_SEX_CD == "male" | PN_SEX_CD == "female") %>% dplyr::group_by(YEAR_ACC.CB, PN_SEX_CD) %>% dplyr::summarise(BADPAPER_MEAN = mean(badpaper.overall, na.rm = TRUE), BADPAPER_SD = sd(badpaper.overall, na.rm = TRUE), n = sum(!is.na(badpaper.overall)))
ct39 <- ct39 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BADPAPER_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BADPAPER_MEAN - MOE, CI.UPPER = BADPAPER_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct39, "Army20Yr_YEARACCbySEXbyBADPAPER_crosstabs.csv")

ct40 <- data %>% dplyr::group_by(YEAR_ACC.CB, RACE_CD_RE) %>% dplyr::summarise(BADPAPER_MEAN = mean(badpaper.overall, na.rm = TRUE), BADPAPER_SD = sd(badpaper.overall, na.rm = TRUE), n = sum(!is.na(badpaper.overall)))
ct40 <- ct40 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BADPAPER_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BADPAPER_MEAN - MOE, CI.UPPER = BADPAPER_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct40, "Army20Yr_YEARACCbyRACEbyBADPAPER_crosstabs.csv")



ct41 <- data %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::summarise(PULHES_MEAN = mean(PULHES.MEAN, na.rm = TRUE), PULHES_SD = sd(PULHES.MEAN, na.rm = TRUE), n = sum(!is.na(PULHES.MEAN)))
ct41 <- ct41 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(PULHES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = PULHES_MEAN - MOE, CI.UPPER = PULHES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct41, "Army20Yr_YEARACCbyPULHES_crosstabs.csv")

ct42 <- data %>% dplyr::group_by(YEAR_ACC.CB, RANK_PDE_GRP) %>% dplyr::summarise(PULHES_MEAN = mean(PULHES.MEAN, na.rm = TRUE), PULHES_SD = sd(PULHES.MEAN, na.rm = TRUE), n = sum(!is.na(PULHES.MEAN)))
ct42 <- ct42 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(PULHES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = PULHES_MEAN - MOE, CI.UPPER = PULHES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct42, "Army20Yr_YEARACCbyRANKGRPbyPULHES_crosstabs.csv")

ct43 <- data %>% dplyr::filter(PN_SEX_CD == "male" | PN_SEX_CD == "female") %>% dplyr::group_by(YEAR_ACC.CB, PN_SEX_CD) %>% dplyr::summarise(PULHES_MEAN = mean(PULHES.MEAN, na.rm = TRUE), PULHES_SD = sd(PULHES.MEAN, na.rm = TRUE), n = sum(!is.na(PULHES.MEAN)))
ct43 <- ct43 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(PULHES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = PULHES_MEAN - MOE, CI.UPPER = PULHES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct43, "Army20Yr_YEARACCbySEXbyPULHES_crosstabs.csv")

ct44 <- data %>% dplyr::group_by(YEAR_ACC.CB, RACE_CD_RE) %>% dplyr::summarise(PULHES_MEAN = mean(PULHES.MEAN, na.rm = TRUE), PULHES_SD = sd(PULHES.MEAN, na.rm = TRUE), n = sum(!is.na(PULHES.MEAN)))
ct44 <- ct44 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(PULHES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = PULHES_MEAN - MOE, CI.UPPER = PULHES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct44, "Army20Yr_YEARACCbyRACEbyPULHES_crosstabs.csv")


ct45 <- data %>% dplyr::group_by(YEAR_ACC.CB, HQ_RECRUIT) %>% dplyr::summarise(BADPAPER_MEAN = mean(badpaper.overall, na.rm = TRUE), BADPAPER_SD = sd(badpaper.overall, na.rm = TRUE), n = sum(!is.na(badpaper.overall)))
ct45 <- ct45 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BADPAPER_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BADPAPER_MEAN - MOE, CI.UPPER = BADPAPER_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct45, "Army20Yr_YEARACCbyHQRECRUITbyBADPAPER_crosstabs.csv")

ct46 <- data %>% dplyr::group_by(YEAR_ACC.CB, MOS_TYPE) %>% dplyr::summarise(BADPAPER_MEAN = mean(badpaper.overall, na.rm = TRUE), BADPAPER_SD = sd(badpaper.overall, na.rm = TRUE), n = sum(!is.na(badpaper.overall)))
ct46 <- ct46 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BADPAPER_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BADPAPER_MEAN - MOE, CI.UPPER = BADPAPER_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct46, "Army20Yr_YEARACCbyMOSTYPEbyBADPAPER_crosstabs.csv")

ct47 <- data %>% dplyr::group_by(YEAR_ACC.CB, MOS_TYPE) %>% dplyr::summarise(PULHES_MEAN = mean(PULHES.MEAN, na.rm = TRUE), PULHES_SD = sd(PULHES.MEAN, na.rm = TRUE), n = sum(!is.na(PULHES.MEAN)))
ct47 <- ct47 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(PULHES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = PULHES_MEAN - MOE, CI.UPPER = PULHES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct47, "Army20Yr_YEARACCbyMOSTYPEbyPULHES_crosstabs.csv")

ct48 <- data %>% dplyr::group_by(YEAR_ACC.CB, HQ_RECRUIT) %>% dplyr::summarise(PULHES_MEAN = mean(PULHES.MEAN, na.rm = TRUE), PULHES_SD = sd(PULHES.MEAN, na.rm = TRUE), n = sum(!is.na(PULHES.MEAN)))
ct48 <- ct48 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(PULHES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = PULHES_MEAN - MOE, CI.UPPER = PULHES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct48, "Army20Yr_YEARACCbyHQRECRUITbyPULHES_crosstabs.csv")



# crosstab of character of service
ct49 <- data %>% dplyr::group_by(YEAR_ACC.CB, CHAR_SVC_CD2) %>% dplyr::summarise(n = n())
ct49 <- ct49 %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::mutate(countT = sum(n)) %>% dplyr::group_by(CHAR_SVC_CD2, add = TRUE) %>% dplyr::mutate(pct = (n/countT)*100) %>% dplyr::select(-countT)
write.csv(ct49, "Army20Yr_YEARACCbyCHRSVC_crosstabs.csv")



ct50 <- data %>% dplyr::group_by(YEAR_ACC.CB, HQ_RECRUIT) %>% dplyr::summarise(APFT_MEAN = mean(APFT_1stSCORE, na.rm = TRUE), APFT_SD = sd(APFT_1stSCORE, na.rm = TRUE), n = sum(!is.na(APFT_1stSCORE)))
ct50 <- ct50 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(APFT_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = APFT_MEAN - MOE, CI.UPPER = APFT_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct50, "Army20Yr_YEARACCbyHQRECRUITbyAPFT_crosstabs.csv")


ct51 <- data %>% dplyr::group_by(YEAR_ACC.CB, MEPCOUNTY5.CB) %>% dplyr::summarise(n = n())
write.csv(ct51, "Army20Yr_YEARACCbyCOUNTY_crosstabs.csv")

#END

## HQ Recruits ======================================

# recode education level to less than H.S. and more than H.S.
levels(data$EDU_LVL_CD)
data <- data %>% dplyr::mutate(EDU_LVL_HS = dplyr::recode(data$EDU_LVL_CD, 
                                                          "adult education diploma" = "H.S. or greater", 
                                                          "ARNG challenge program GED cert." = "H.S. or greater", 
                                                          "associate degree" = "H.S. or greater", 
                                                          "baccalureate" = "H.S. or greater", 
                                                          "completed one semester of college, no H.S." = "Less than H.S.", 
                                                          "coorespondence school diploma" = "H.S. or greater", 
                                                          "doctorate degree" = "H.S. or greater", 
                                                          "first prof. degree" = "H.S. or greater", 
                                                          "H.S. cert of attendance" = "Less than H.S.", 
                                                          "H.S. diploma" = "H.S. or greater", 
                                                          "home study diploma" = "H.S. or greater", 
                                                          "less than H.S." = "Less than H.S.", 
                                                          "master degree" = "H.S. or greater", 
                                                          "occupational program cert." = "H.S. or greater", 
                                                          "Other non-traditional H.S. credential" = "H.S. or greater", 
                                                          "post-doc degree" = "H.S. or greater", 
                                                          "post master degree" = "H.S. or greater", 
                                                          "prof. nursing diploma" = "H.S. or greater", 
                                                          "secondary school credential near completion" = "Less than H.S.", 
                                                          "test-based equivalency diploma" = "H.S. or greater"))
levels(data$EDU_LVL_HS)

data <- data %>% dplyr::mutate(HQ_RECRUIT = ifelse(EDU_LVL_HS == "H.S. or greater" & AFQT_PCTL.CB > 50, "High Quality Recruit", "Low Quality Recruit"))
data %>% dplyr::select(EDU_LVL_CD, EDU_LVL_HS, AFQT_PCTL.CB, HQ_RECRUIT)


rq1 <- data %>% dplyr::filter(!is.na(HQ_RECRUIT)) %>% dplyr::group_by(YEAR_ACC.CB, HQ_RECRUIT) %>% dplyr::summarise(n = n())
rq1 <- rq1 %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::mutate(countT = sum(n)) %>% dplyr::group_by(HQ_RECRUIT, add = TRUE) %>% dplyr::mutate(pct = (n/countT)*100) %>% dplyr::select(-countT)
write.csv(rq1, "Army20Yr_YearACCbyHQRECRUIT_crosstabs.csv")


rq2 <- data %>% dplyr::filter(!is.na(HQ_RECRUIT) & PN_SEX_CD != "unknown") %>% dplyr::group_by(YEAR_ACC.CB, PN_SEX_CD, HQ_RECRUIT) %>% dplyr::summarise(n = n())
rq2 <- rq2 %>% dplyr::group_by(YEAR_ACC.CB, PN_SEX_CD) %>% dplyr::mutate(countT = sum(n)) %>% dplyr::group_by(HQ_RECRUIT, add = TRUE) %>% dplyr::mutate(pct = (n/countT)*100) %>% dplyr::select(-countT)
write.csv(rq2, "Army20Yr_YearACCbySEXbyHQRECRUIT_crosstabs.csv")

rq3 <- data %>% dplyr::filter(!is.na(HQ_RECRUIT) & RANK_PDE_GRP != "Warrant Officer") %>% dplyr::group_by(YEAR_ACC.CB, RANK_PDE_GRP, HQ_RECRUIT) %>% dplyr::summarise(n = n())
rq3 <- rq3 %>% dplyr::group_by(YEAR_ACC.CB, RANK_PDE_GRP) %>% dplyr::mutate(countT = sum(n)) %>% dplyr::group_by(HQ_RECRUIT, add = TRUE) %>% dplyr::mutate(pct = (n/countT)*100) %>% dplyr::select(-countT)
write.csv(rq3, "Army20Yr_YearACCbyRANKGRPbyHQRECRUIT_crosstabs.csv")

levels(data$RACE_CD_RE)
rq4 <- data %>% dplyr::filter(!is.na(HQ_RECRUIT), RACE_CD_RE == c("white", "black", "asian")) %>% dplyr::group_by(YEAR_ACC.CB, RACE_CD_RE, HQ_RECRUIT) %>% dplyr::summarise(n = n())
rq4 <- rq4 %>% dplyr::group_by(YEAR_ACC.CB, RACE_CD_RE) %>% dplyr::mutate(countT = sum(n)) %>% dplyr::group_by(HQ_RECRUIT, add = TRUE) %>% dplyr::mutate(pct = (n/countT)*100) %>% dplyr::select(-countT)
write.csv(rq4, "Army20Yr_YearACCbyRACEbyHQRECRUIT_crosstabs.csv")

rq5 <- data %>% dplyr::filter(!is.na(HQ_RECRUIT), BMI < 42.92, BMI > 6.26) %>% dplyr::group_by(YEAR_ACC.CB, HQ_RECRUIT) %>% dplyr::summarise(BMI_MEAN = mean(BMI, na.rm = TRUE), BMI_SD = sd(BMI, na.rm = TRUE), n = sum(!is.na(BMI)))
rq5 <- rq5 %>%  dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BMI_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BMI_MEAN - MOE, CI.UPPER = BMI_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(rq5, "Army20Yr_YEARACCbyHQRECRUITbyBMI_crosstabs.csv")




ct10b <- data %>% dplyr::filter(BMI < 42.92, BMI > 6.26) %>% dplyr::group_by(YEAR_ACC.CB, RACE.CT) %>% dplyr::summarise(BMI_MEAN = mean(BMI, na.rm = TRUE), BMI_SD = sd(BMI, na.rm = TRUE), n = sum(!is.na(BMI)))
ct10b <- ct10b %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(BMI_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = BMI_MEAN - MOE, CI.UPPER = BMI_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ct10b, "Army20Yr_YEARACCbyRACEbyBMI_crosstabs.csv")



#END


## Hollingshead Two-Factor SES ======================================

# recode education level to less than H.S. and more than H.S.
# Hollingshead (2011) level of school completed coding: 1 = less than seventh grade, 2 = junior high school (9th grade), 3 = partial high school (10th grade or 11th grade), 4 = high school graduate or equivalent, 
#                                                5 = partial college (at least one year) or specilized training, 6 = standard college or university graduation, 7 = graduate professional training (graduate degegree)

levels(data$EDU_LVL_CD)
data <- data %>% dplyr::mutate(EDU_LVL_HOLLHEAD = dplyr::recode(data$EDU_LVL_CD, 
                                                                "adult education diploma" = 4, 
                                                                "ARNG challenge program GED cert." = 4, 
                                                                "associate degree" = 5, 
                                                                "baccalureate" = 6, 
                                                                "completed one semester of college, no H.S." = 3, 
                                                                "coorespondence school diploma" = 4, 
                                                                "doctorate degree" = 7, 
                                                                "first prof. degree" = 6, 
                                                                "H.S. cert of attendance" = 3, 
                                                                "H.S. diploma" = 4, 
                                                                "home study diploma" = 4, 
                                                                "less than H.S." = 3, 
                                                                "master degree" = 7, 
                                                                "occupational program cert." = 5, 
                                                                "Other non-traditional H.S. credential" = 4, 
                                                                "post-doc degree" = 7, 
                                                                "post master degree" = 7, 
                                                                "prof. nursing diploma" = 5, 
                                                                "secondary school credential near completion" = 5, 
                                                                "test-based equivalency diploma" = 4))
class(data$EDU_LVL_HOLLHEAD)

# Hollingstead (2011) Occupation Scale: 1 = laborers, 2 = unskilled workers, 3 = all enlisted below NCO, 4 = NCOs (below rank MSG), 
#                                       5 = small business owners (?), 6 = semiprofessionals (MSG & above), 7 = minor professionals (WOs & CWOs), 8 = commisioned officer (2LT, 1LT, CPT, sg, jg), 9 = Commisioned officer (MAJ and above)

levels(data$RANK_PDE)
data <- data %>% dplyr::mutate(OCCUPATION_HOLLHEAD = dplyr::recode(data$RANK_PDE,
                                                                   "1LT" = 8,
                                                                   "2LT" = 8,
                                                                   "CPL" = 3,
                                                                   "CPT" = 8,
                                                                   "CW2" = 7,
                                                                   "CW3" = 7,
                                                                   "EEE" = 6,
                                                                   "MAJ" = 9,
                                                                   "OOO" = 9,
                                                                   "PFC" = 3,
                                                                   "PV1" = 3,
                                                                   "PV2" = 3,
                                                                   "SFC" = 4,
                                                                   "SGT" = 4,
                                                                   "SSG" = 4,
                                                                   "WO1" = 7,
                                                                   "WWW" = 7))

class(data$OCCUPATION_HOLLHEAD)

# Calculate Hollingshead Two-Factor SES: EDU_LVL*3 + OCC_LVL*5
data <- data %>% dplyr::mutate(TFSES_HOLLHEAD = ((EDU_LVL_HOLLHEAD * 3) + (OCCUPATION_HOLLHEAD * 5)))
data %>% dplyr::select(EDU_LVL_CD, RANK_PDE, EDU_LVL_HOLLHEAD, OCCUPATION_HOLLHEAD, TFSES_HOLLHEAD)
class(data$TFSES_HOLLHEAD)
unique(data$TFSES_HOLLHEAD)


ses1 <- data %>% dplyr::group_by(YEAR_ACC.CB) %>% dplyr::summarise(SES_MEAN = mean(TFSES_HOLLHEAD, na.rm = TRUE), SES_SD = sd(TFSES_HOLLHEAD, na.rm = TRUE), n = sum(!is.na(TFSES_HOLLHEAD)))
ses1 <- ses1 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(SES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = SES_MEAN - MOE, CI.UPPER = SES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ses1, "Army20Yr_YEARACCbySES_crosstabs.csv")


ses2 <- data %>% dplyr::filter(PN_SEX_CD != "unknown") %>% dplyr::group_by(YEAR_ACC.CB, PN_SEX_CD) %>% dplyr::summarise(SES_MEAN = mean(TFSES_HOLLHEAD, na.rm = TRUE), SES_SD = sd(TFSES_HOLLHEAD, na.rm = TRUE), n = sum(!is.na(TFSES_HOLLHEAD)))
ses2 <- ses2 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(SES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = SES_MEAN - MOE, CI.UPPER = SES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ses2, "Army20Yr_YEARACCbySEXbySES_crosstabs.csv")

ses3 <- data %>% dplyr::filter(RACE_CD_RE == c("white", "black", "asian")) %>% dplyr::group_by(YEAR_ACC.CB, RACE_CD_RE) %>% dplyr::summarise(SES_MEAN = mean(TFSES_HOLLHEAD, na.rm = TRUE), SES_SD = sd(TFSES_HOLLHEAD, na.rm = TRUE), n = sum(!is.na(TFSES_HOLLHEAD)))
ses3 <- ses3 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(SES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = SES_MEAN - MOE, CI.UPPER = SES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ses3, "Army20Yr_YEARACCbyRACEbySES_crosstabs.csv")


ses4 <- data %>% dplyr::group_by(zipcode3) %>% dplyr::summarise(SES_MEAN = mean(TFSES_HOLLHEAD, na.rm = TRUE), SES_SD = sd(TFSES_HOLLHEAD, na.rm = TRUE), n = sum(!is.na(TFSES_HOLLHEAD)))
ses4 <- ses4 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(SES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = SES_MEAN - MOE, CI.UPPER = SES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ses4, "Army20Yr_ZIP3bySES_crosstabs.csv")


ses5 <- data %>% dplyr::group_by(YEAR_ACC.CB, zipcode3) %>% dplyr::summarise(SES_MEAN = mean(TFSES_HOLLHEAD, na.rm = TRUE), SES_SD = sd(TFSES_HOLLHEAD, na.rm = TRUE), n = sum(!is.na(TFSES_HOLLHEAD)))
ses5 <- ses5 %>% dplyr::mutate(MOE = 1.41*(qt(1-.05/2, n - 1))*(SES_SD/(sqrt(n)))) %>% dplyr::mutate(CI.LOWER = SES_MEAN - MOE, CI.UPPER = SES_MEAN + MOE) # calc CI with correction factor [1.41] Cousineau (2017)
write.csv(ses5, "Army20Yr_YEARACCbyZIP3bySES_crosstabs.csv")


