rm(list=ls())

library(chron)
library(colorspace)
library(mime)
library(dichromat)
library(munsell)
library(labeling)
library(rlang)
library(stringi)
library(evaluate)
library(highr)
library(markdown)
library(yaml)
library(backports)
library(jsonlite)
library(digest)
library(plyr)
library(reshape2)
library(scales)
library(tibble)
library(lazyeval)
library(RColorBrewer)
library(stringr)
library(knitr)
library(magrittr)
library(checkmate)
library(htmlwidgets)
library(viridisLite)
library(Rcpp)
library(Formula)
library(ggplot2)
library(latticeExtra)
library(acepack)
library(gtable)
library(gridExtra)
library(data.table)
library(htmlTable)
library(viridis)
library(htmltools)
library(base64enc)
library(minqa)
library(RcppEigen)
library(lme4)
library(SparseM)
library(MatrixModels)
library(pbkrtest)
library(quantreg)
library(car)
library(htmlTable)
library(Hmisc)
library(survival)
library(foreign)
library(bitops)
library(caTools)
library(gplots)
library(ROCR)
library(RODBC)
library(compareGroups)
library(nlme)
library(vcd)
library(psy)
library(irr)
library(boot)
library(tibble)
library(haven)
library(icenReg)
library(arm)
library(standardize)
library(MASS)
library(sandwich)   
library(lmtest)
library(gam)
library(smoothHR)
library(meta)
library(metafor)

guapa<-function(x)
{
  redondeo<-ifelse(abs(x)<0.00001,signif(x,1),
                   ifelse(abs(x)<0.0001,signif(x,1),
                          ifelse(abs(x)<0.001,signif(x,1),
                                 ifelse(abs(x)<0.1,sprintf("%.3f",round(x,3)),
                                        ifelse(abs(x)<1,sprintf("%.2f",round(x,2)),
                                               ifelse(abs(x)<10,sprintf("%.2f",round(x,2)),
                                                      ifelse(abs(x)<100,sprintf("%.1f",round(x,1)),
                                                             ifelse(abs(x)>=100,round(x,0),round(x,0)))))))))
  return(redondeo)
}

ic_guapa<-function(x,y,z)
{
  ic<-paste(x," [",y,"; ",z,"]",sep="")
  return(ic)
}

pval_guapa<-function(x)
{
  pval<-ifelse(x<0.00001,"<0.00001",
               ifelse(x<0.001,"<0.001",round(x,3)))
  return(pval)
}

mean_ic_guapa <- function(x, na.rm=FALSE) 
{
  if (na.rm) x <- na.omit(x)
  se<-sqrt(var(x)/length(x))
  z<-qnorm(1-0.05/2)
  media<-mean(x)
  ic95a<-guapa(media-(z*se))
  ic95b<-guapa(media+(z*se))
  media<-guapa(media)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

mean_sd_guapa <- function(x) 
{
  media<-guapa(mean(x, na.rm=TRUE))
  sd<-guapa(sd(x, na.rm=TRUE))
  end<-paste(media," (",sd,")",sep="")
  return(end)
}

beta_se_ic_guapa <- function(x, y) 
{
  z<-qnorm(1-0.05/2)
  ic95a<-guapa(x-(z*y))
  ic95b<-guapa(x+(z*y))
  media<-guapa(x)
  ic_ok<-ic_guapa(media,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-guapa(exp(x))
  ic95a<-guapa(exp(x-(z*y)))
  ic95b<-guapa(exp(x+(z*y)))
  ic_ok<-ic_guapa(hr,ic95a,ic95b)
  return(ic_ok)
}

risk_se_ic_guapa2 <- function(x,y) 
{
  z<-qnorm(1-0.05/2)
  hr<-round(exp(x),5)
  ic95a<-round(exp(x-(z*y)),5)
  ic95b<-round(exp(x+(z*y)),5)
  ic_ok<-ic_guapa(hr,ic95a,ic95b)
  return(ic_ok)
}

header.true <- function(df)
{
  names(df) <- as.character(unlist(df[1,]))
  df[-1,]
}

####EFFECT OF CHARGE####
##### NEGATIVE #####
setwd("")

dat<-read.csv2("./",header=TRUE,sep=";",dec=".")
z<-qnorm(1-0.05/2)

dat$beta<-with(dat,ifelse(!is.na(diff_beta),diff_beta,
                          ifelse(is.na(diff_beta),group1_beta-group2_beta,NA)))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_lo), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_lo), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_lo), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_lo),(group1_lo-group1_beta)/-z, NA)))))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_sd), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_sd), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_sd), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_sd),group1_sd/sqrt(group1_n), NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_lo), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_lo), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_lo), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_lo),(group2_lo-group2_beta)/-z, NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_sd), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_sd), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_sd), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_sd),group2_sd/sqrt(group2_n), NA)))))
dat$se<-with(dat,ifelse(!is.na(diff_se),diff_se,
                        ifelse(is.na(diff_se),sqrt(group1_se^2 + group2_se^2),NA)))
dat$n<-with(dat,ifelse(!is.na(diff_n),diff_n,
                       ifelse(is.na(diff_n),as.numeric(dat$group1_n)+as.numeric(dat$group2_n),NA)))

meta<-metagen(TE = dat$beta,
              seTE = dat$se,
              studlab = dat$author,
              data = dat,
              sm = "MD",
              method.tau = "REML",
              hakn = TRUE,
              prediction = FALSE,
              title = c("BW"))

coef_fixed<-ic_guapa(guapa(meta$TE.fixed),guapa(meta$lower.fixed),guapa(meta$upper.fixed))
pval_fixed<-round(meta$pval.fixed,5)
beta_fixed<-round(meta$TE.fixed,5)
ic95lo_fixed<-round(meta$lower.fixed,5)
ic95hi_fixed<-round(meta$upper.fixed,5)

coef_random<-ic_guapa(guapa(meta$TE.random),guapa(meta$lower.random),guapa(meta$upper.random))
pval_random<-round(meta$pval.random,5)
beta_random<-round(meta$TE.random,5)
ic95lo_random<-round(meta$lower.random,5)
ic95hi_random<-round(meta$upper.random,5)

i2<-guapa(meta$I2)
suma<-sum(as.numeric(dat$n))

tab<-NULL
tab<-rbind(tab,cbind(coef_fixed,pval_fixed,beta_fixed,ic95lo_fixed,ic95hi_fixed,
                     coef_random,pval_random,beta_random,ic95lo_random,ic95hi_random,i2,suma))

rownames(tab)<-c("bw")
write.table(tab,file="./",sep=";",col.names=NA)

jpeg(filename = "./", 
     width = 14000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 1.2, mar = c(6, 6, 2, 0), bty = "n", lheight = 0.9)
forest(meta, xlim=c(-600, 600), pch=10, col.diamond="#0072b2", col.diamond.lines = "#0072b2", col.random = "#0072b2", col.diamond.common = "gray35", col.diamond.lines.common = "gray35", col.common = "gray35",  col.square = "#00a3ff", col.square.lines = "#00a3ff", col.study = "#004166", col.lines = "gray5")
dev.off()

meta_analysis <- metagen(
  TE = dat$beta,
  seTE = dat$se,
  studlab = dat$author,
  sm = "MD" 
)

jpeg(filename = "./",
     width = 16000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 0.9, mar = c(6, 6, 2, 2), bty = "o", lheight = 0.1)
funnel(meta_analysis, main = "Funnel Plot of Meta-Analysis", labels = TRUE, cex = 0.5)
text(x = meta_analysis$TE, y = meta_analysis$seTE, labels =  dat$author , pos = 3, cex = 0.5, srt = 45, col="black")
dev.off()

meta$n.e <- dat$group1_n  
meta$n.c <- dat$group2_n  

egger_test <- metabias(meta, method.bias = "Pustejovsky")
print(egger_test)

egger_test <- metabias(meta, method.bias = "linreg")
print(egger_test)


#####POSITIVE#####
setwd("")

dat<-read.csv2("./",header=TRUE,sep=";",dec=".")
z<-qnorm(1-0.05/2)
dat$beta<-with(dat,ifelse(!is.na(diff_beta),diff_beta,
                          ifelse(is.na(diff_beta),group1_beta-group2_beta,NA)))
dat$lo<-with(dat,ifelse(!is.na(diff_lo),diff_lo,
                        ifelse(is.na(diff_lo),group1_lo-group2_lo,NA)))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se), group1_se,
                                ifelse(is.na(group1_se),(group1_lo-group1_beta)/-z, NA)))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se), group2_se,
                                ifelse(is.na(group2_se),(group2_lo-group2_beta)/-z, NA)))
dat$group1_sd<-with(dat, ifelse(!is.na(group1_sd), group1_sd,
                                ifelse(is.na(group1_sd), group1_se*sqrt(group1_n), NA)))
dat$group2_sd<-with(dat, ifelse(!is.na(group2_sd), group2_sd,
                                ifelse(is.na(group2_sd), group2_se*sqrt(group2_n), NA)))
dat$group1_sem<-dat$group1_sd/sqrt(dat$group1_n)
dat$group2_sem<-dat$group2_sd/sqrt(dat$group2_n)
dat$se<-with(dat,ifelse(!is.na(diff_se),diff_se,
                        ifelse(is.na(diff_se),sqrt(group1_sem^2 + group2_sem^2),NA))) 
dat$n<-with(dat,ifelse(!is.na(diff_n),diff_n,
                       ifelse(is.na(diff_n),as.numeric(dat$group1_n)+as.numeric(dat$group2_n),NA)))

meta<-metagen(TE = dat$beta,
              seTE = dat$se,
              studlab = dat$author,
              data = dat,
              sm = "MD",
              method.tau = "REML",
              hakn = TRUE,
              prediction = FALSE,
              title = c("BW"))

coef_fixed<-ic_guapa(guapa(meta$TE.fixed),guapa(meta$lower.fixed),guapa(meta$upper.fixed))
pval_fixed<-round(meta$pval.fixed,5)
beta_fixed<-round(meta$TE.fixed,5)
ic95lo_fixed<-round(meta$lower.fixed,5)
ic95hi_fixed<-round(meta$upper.fixed,5)

coef_random<-ic_guapa(guapa(meta$TE.random),guapa(meta$lower.random),guapa(meta$upper.random))
pval_random<-round(meta$pval.random,5)
beta_random<-round(meta$TE.random,5)
ic95lo_random<-round(meta$lower.random,5)
ic95hi_random<-round(meta$upper.random,5)

i2<-guapa(meta$I2)
suma<-sum(as.numeric(dat$n))

tab<-NULL
tab<-rbind(tab,cbind(coef_fixed,pval_fixed,beta_fixed,ic95lo_fixed,ic95hi_fixed,
                     coef_random,pval_random,beta_random,ic95lo_random,ic95hi_random,i2,suma))

rownames(tab)<-c("bw")
write.table(tab,file="./",sep=";",col.names=NA)

jpeg(filename = "./", 
     width = 14000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 1.2, mar = c(6, 6, 2, 0), bty = "n", lheight = 0.9)
forest(meta, xlim=c(-600, 600), pch=10, col.diamond="#0072b2", col.diamond.lines = "#0072b2", col.random = "#0072b2", col.diamond.common = "gray35", col.diamond.lines.common = "gray35", col.common = "gray35",  col.square = "#00a3ff", col.square.lines = "#00a3ff", col.study = "#004166", col.lines = "gray5")
dev.off()

jpeg(filename = "./",
     width = 16000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 0.9, mar = c(6, 6, 2, 2), bty = "o", lheight = 0.1)
funnel(meta_analysis, main = "Funnel Plot of Meta-Analysis", labels = TRUE, cex = 0.5)
text(x = meta_analysis$TE, y = meta_analysis$seTE, labels =  dat$author , pos = 3, cex = 0.5, srt = 45, col="black")
dev.off()

meta$n.e <- dat$group1_n  
meta$n.c <- dat$group2_n  

egger_test <- metabias(meta, method.bias = "Pustejovsky")
print(egger_test)

egger_test <- metabias(meta, method.bias = "linreg")
print(egger_test)


####EFFECT OF COMPOSITION#####

#####PLAIN INORGANIC#####
setwd("")

dat<-read.csv2("./",header=TRUE,sep=";",dec=".")
z<-qnorm(1-0.05/2)

dat$beta<-with(dat,ifelse(!is.na(diff_beta),diff_beta,
                          ifelse(is.na(diff_beta),group1_beta-group2_beta,NA)))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_lo), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_lo), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_lo), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_lo),(group1_lo-group1_beta)/-z, NA)))))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_sd), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_sd), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_sd), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_sd),group1_sd/sqrt(group1_n), NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_lo), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_lo), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_lo), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_lo),(group2_lo-group2_beta)/-z, NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_sd), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_sd), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_sd), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_sd),group2_sd/sqrt(group2_n), NA)))))
dat$se<-with(dat,ifelse(!is.na(diff_se),diff_se,
                        ifelse(is.na(diff_se),sqrt(group1_se^2 + group2_se^2),NA)))
dat$n<-with(dat,ifelse(!is.na(diff_n),diff_n,
                       ifelse(is.na(diff_n),as.numeric(dat$group1_n)+as.numeric(dat$group2_n),NA)))

meta<-metagen(TE = dat$beta,
              seTE = dat$se,
              studlab = dat$author,
              data = dat,
              sm = "MD",
              method.tau = "REML",
              hakn = TRUE,
              prediction = FALSE,
              title = c("BW"))

coef_fixed<-ic_guapa(guapa(meta$TE.fixed),guapa(meta$lower.fixed),guapa(meta$upper.fixed))
pval_fixed<-round(meta$pval.fixed,5)
beta_fixed<-round(meta$TE.fixed,5)
ic95lo_fixed<-round(meta$lower.fixed,5)
ic95hi_fixed<-round(meta$upper.fixed,5)

coef_random<-ic_guapa(guapa(meta$TE.random),guapa(meta$lower.random),guapa(meta$upper.random))
pval_random<-round(meta$pval.random,5)
beta_random<-round(meta$TE.random,5)
ic95lo_random<-round(meta$lower.random,5)
ic95hi_random<-round(meta$upper.random,5)

i2<-guapa(meta$I2)
suma<-sum(as.numeric(dat$n))

tab<-NULL
tab<-rbind(tab,cbind(coef_fixed,pval_fixed,beta_fixed,ic95lo_fixed,ic95hi_fixed,
                     coef_random,pval_random,beta_random,ic95lo_random,ic95hi_random,i2,suma))

rownames(tab)<-c("bw")
write.table(tab,file="./",sep=";",col.names=NA)

jpeg(filename = "./.jpg", 
     width = 14000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 1.2, mar = c(6, 6, 2, 0), bty = "n", lheight = 0.9)
forest(meta, xlim=c(-600, 600), pch=10, col.diamond="#b44582", col.diamond.lines = "#b44582", col.random = "#b44582", col.diamond.common = "gray35", col.diamond.lines.common = "gray35", col.common = "gray35",  col.square = "#e1b0cb", col.square.lines = "#e1b0cb", col.study = "#cc79a7", col.lines = "gray5")
dev.off()

jpeg(filename = "./",
     width = 16000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 0.9, mar = c(6, 6, 2, 2), bty = "o", lheight = 0.1)
funnel(meta_analysis, main = "Funnel Plot of Meta-Analysis", labels = TRUE, cex = 0.5)
text(x = meta_analysis$TE, y = meta_analysis$seTE, labels =  dat$author , pos = 3, cex = 0.5, srt = 45, col="black")
dev.off()

meta$n.e <- dat$group1_n  
meta$n.c <- dat$group2_n  

egger_test <- metabias(meta, method.bias = "Pustejovsky")
print(egger_test)

egger_test <- metabias(meta, method.bias = "linreg")
print(egger_test)


#####INROGANIC COATED WITH SMALL MOLECULES#####
setwd("")

dat<-read.csv2("./",header=TRUE,sep=";",dec=".")
z<-qnorm(1-0.05/2)

dat$beta<-with(dat,ifelse(!is.na(diff_beta),diff_beta,
                          ifelse(is.na(diff_beta),group1_beta-group2_beta,NA)))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_lo), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_lo), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_lo), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_lo),(group1_lo-group1_beta)/-z, NA)))))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_sd), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_sd), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_sd), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_sd),group1_sd/sqrt(group1_n), NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_lo), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_lo), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_lo), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_lo),(group2_lo-group2_beta)/-z, NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_sd), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_sd), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_sd), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_sd),group2_sd/sqrt(group2_n), NA)))))
dat$se<-with(dat,ifelse(!is.na(diff_se),diff_se,
                        ifelse(is.na(diff_se),sqrt(group1_se^2 + group2_se^2),NA)))
dat$n<-with(dat,ifelse(!is.na(diff_n),diff_n,
                       ifelse(is.na(diff_n),as.numeric(dat$group1_n)+as.numeric(dat$group2_n),NA)))

meta<-metagen(TE = dat$beta,
              seTE = dat$se,
              studlab = dat$author,
              data = dat,
              sm = "MD",
              method.tau = "REML",
              hakn = TRUE,
              prediction = FALSE,
              title = c("BW"))

coef_fixed<-ic_guapa(guapa(meta$TE.fixed),guapa(meta$lower.fixed),guapa(meta$upper.fixed))
pval_fixed<-round(meta$pval.fixed,5)
beta_fixed<-round(meta$TE.fixed,5)
ic95lo_fixed<-round(meta$lower.fixed,5)
ic95hi_fixed<-round(meta$upper.fixed,5)

coef_random<-ic_guapa(guapa(meta$TE.random),guapa(meta$lower.random),guapa(meta$upper.random))
pval_random<-round(meta$pval.random,5)
beta_random<-round(meta$TE.random,5)
ic95lo_random<-round(meta$lower.random,5)
ic95hi_random<-round(meta$upper.random,5)

i2<-guapa(meta$I2)
suma<-sum(as.numeric(dat$n))

tab<-NULL
tab<-rbind(tab,cbind(coef_fixed,pval_fixed,beta_fixed,ic95lo_fixed,ic95hi_fixed,
                     coef_random,pval_random,beta_random,ic95lo_random,ic95hi_random,i2,suma))

rownames(tab)<-c("bw")
write.table(tab,file="./",sep=";",col.names=NA)

jpeg(filename = "./", 
     width = 14000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 1.2, mar = c(6, 6, 2, 0), bty = "n", lheight = 0.9)
forest(meta, xlim=c(-600, 600), pch=10, col.diamond="#b44582", col.diamond.lines = "#b44582", col.random = "#b44582", col.diamond.common = "gray35", col.diamond.lines.common = "gray35", col.common = "gray35",  col.square = "#e1b0cb", col.square.lines = "#e1b0cb", col.study = "#cc79a7", col.lines = "gray5")
dev.off()

jpeg(filename = "./",
     width = 16000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 0.9, mar = c(6, 6, 2, 2), bty = "o", lheight = 0.1)
funnel(meta_analysis, main = "Funnel Plot of Meta-Analysis", labels = TRUE, cex = 0.5)
text(x = meta_analysis$TE, y = meta_analysis$seTE, labels =  dat$author , pos = 3, cex = 0.5, srt = 45, col="black")
dev.off()

meta$n.e <- dat$group1_n  
meta$n.c <- dat$group2_n  

egger_test <- metabias(meta, method.bias = "Pustejovsky")
print(egger_test)

egger_test <- metabias(meta, method.bias = "linreg")
print(egger_test)


#####POLYMER COATED#####
setwd("")

dat<-read.csv2("./",header=TRUE,sep=";",dec=".")
z<-qnorm(1-0.05/2)

dat$beta<-with(dat,ifelse(!is.na(diff_beta),diff_beta,
                          ifelse(is.na(diff_beta),group1_beta-group2_beta,NA)))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_lo), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_lo), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_lo), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_lo),(group1_lo-group1_beta)/-z, NA)))))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_sd), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_sd), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_sd), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_sd),group1_sd/sqrt(group1_n), NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_lo), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_lo), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_lo), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_lo),(group2_lo-group2_beta)/-z, NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_sd), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_sd), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_sd), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_sd),group2_sd/sqrt(group2_n), NA)))))
dat$se<-with(dat,ifelse(!is.na(diff_se),diff_se,
                        ifelse(is.na(diff_se),sqrt(group1_se^2 + group2_se^2),NA)))
dat$n<-with(dat,ifelse(!is.na(diff_n),diff_n,
                       ifelse(is.na(diff_n),as.numeric(dat$group1_n)+as.numeric(dat$group2_n),NA)))

meta<-metagen(TE = dat$beta,
              seTE = dat$se,
              studlab = dat$author,
              data = dat,
              sm = "MD",
              method.tau = "REML",
              hakn = TRUE,
              prediction = FALSE,
              title = c("BW"))

coef_fixed<-ic_guapa(guapa(meta$TE.fixed),guapa(meta$lower.fixed),guapa(meta$upper.fixed))
pval_fixed<-round(meta$pval.fixed,5)
beta_fixed<-round(meta$TE.fixed,5)
ic95lo_fixed<-round(meta$lower.fixed,5)
ic95hi_fixed<-round(meta$upper.fixed,5)

coef_random<-ic_guapa(guapa(meta$TE.random),guapa(meta$lower.random),guapa(meta$upper.random))
pval_random<-round(meta$pval.random,5)
beta_random<-round(meta$TE.random,5)
ic95lo_random<-round(meta$lower.random,5)
ic95hi_random<-round(meta$upper.random,5)

i2<-guapa(meta$I2)
suma<-sum(as.numeric(dat$n))

tab<-NULL
tab<-rbind(tab,cbind(coef_fixed,pval_fixed,beta_fixed,ic95lo_fixed,ic95hi_fixed,
                     coef_random,pval_random,beta_random,ic95lo_random,ic95hi_random,i2,suma))

rownames(tab)<-c("bw")
write.table(tab,file="./",sep=";",col.names=NA)

jpeg(filename = "./", 
     width = 14000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 1.2, mar = c(6, 6, 2, 0), bty = "n", lheight = 0.9)
forest(meta, xlim=c(-600, 600), pch=10, col.diamond="#b44582", col.diamond.lines = "#b44582", col.random = "#b44582", col.diamond.common = "gray35", col.diamond.lines.common = "gray35", col.common = "gray35",  col.square = "#e1b0cb", col.square.lines = "#e1b0cb", col.study = "#cc79a7", col.lines = "gray5")
dev.off()

jpeg(filename = "./",
     width = 16000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 0.9, mar = c(6, 6, 2, 2), bty = "o", lheight = 0.1)
funnel(meta_analysis, main = "Funnel Plot of Meta-Analysis", labels = TRUE, cex = 0.5)
text(x = meta_analysis$TE, y = meta_analysis$seTE, labels =  dat$author , pos = 3, cex = 0.5, srt = 45, col="black")
dev.off()

meta$n.e <- dat$group1_n 
meta$n.c <- dat$group2_n  

egger_test <- metabias(meta, method.bias = "Pustejovsky")
print(egger_test)

egger_test <- metabias(meta, method.bias = "linreg")
print(egger_test)


####EFFECT OF SIZE#####

#####LARGE#####
setwd("")

dat<-read.csv2("./",header=TRUE,sep=";",dec=".")
z<-qnorm(1-0.05/2)

dat$beta<-with(dat,ifelse(!is.na(diff_beta),diff_beta,
                          ifelse(is.na(diff_beta),group1_beta-group2_beta,NA)))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_lo), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_lo), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_lo), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_lo),(group1_lo-group1_beta)/-z, NA)))))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_sd), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_sd), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_sd), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_sd),group1_sd/sqrt(group1_n), NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_lo), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_lo), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_lo), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_lo),(group2_lo-group2_beta)/-z, NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_sd), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_sd), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_sd), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_sd),group2_sd/sqrt(group2_n), NA)))))
dat$se<-with(dat,ifelse(!is.na(diff_se),diff_se,
                        ifelse(is.na(diff_se),sqrt(group1_se^2 + group2_se^2),NA)))
dat$n<-with(dat,ifelse(!is.na(diff_n),diff_n,
                       ifelse(is.na(diff_n),as.numeric(dat$group1_n)+as.numeric(dat$group2_n),NA)))

meta<-metagen(TE = dat$beta,
              seTE = dat$se,
              studlab = dat$author,
              data = dat,
              sm = "MD",
              method.tau = "REML",
              hakn = TRUE,
              prediction = FALSE,
              title = c("BW"))

coef_fixed<-ic_guapa(guapa(meta$TE.fixed),guapa(meta$lower.fixed),guapa(meta$upper.fixed))
pval_fixed<-round(meta$pval.fixed,5)
beta_fixed<-round(meta$TE.fixed,5)
ic95lo_fixed<-round(meta$lower.fixed,5)
ic95hi_fixed<-round(meta$upper.fixed,5)

coef_random<-ic_guapa(guapa(meta$TE.random),guapa(meta$lower.random),guapa(meta$upper.random))
pval_random<-round(meta$pval.random,5)
beta_random<-round(meta$TE.random,5)
ic95lo_random<-round(meta$lower.random,5)
ic95hi_random<-round(meta$upper.random,5)

i2<-guapa(meta$I2)
suma<-sum(as.numeric(dat$n))

tab<-NULL
tab<-rbind(tab,cbind(coef_fixed,pval_fixed,beta_fixed,ic95lo_fixed,ic95hi_fixed,
                     coef_random,pval_random,beta_random,ic95lo_random,ic95hi_random,i2,suma))

rownames(tab)<-c("bw")
write.table(tab,file="./",sep=";",col.names=NA)

jpeg(filename = "./", 
     width = 14000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 1.2, mar = c(6, 6, 2, 0), bty = "n", lheight = 0.9)
forest(meta, xlim=c(-600, 600), pch=10, col.diamond="#257622", col.diamond.lines = "#257622", col.random = "#257622", col.diamond.common = "gray35", col.diamond.lines.common = "gray35", col.common = "gray35",  col.square = "#38b334", col.square.lines = "#38b334", col.study = "#2f942b", col.lines = "gray5")
dev.off()

jpeg(filename = "./",
     width = 16000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 0.9, mar = c(6, 6, 2, 2), bty = "o", lheight = 0.1)
funnel(meta_analysis, main = "Funnel Plot of Meta-Analysis", labels = TRUE, cex = 0.5)
text(x = meta_analysis$TE, y = meta_analysis$seTE, labels =  dat$author , pos = 3, cex = 0.5, srt = 45, col="black")
dev.off()

meta$n.e <- dat$group1_n  
meta$n.c <- dat$group2_n  

egger_test <- metabias(meta, method.bias = "Pustejovsky")
print(egger_test)

egger_test <- metabias(meta, method.bias = "linreg")
print(egger_test)


#####MEDIUM#####
setwd("")

dat<-read.csv2("./",header=TRUE,sep=";",dec=".")
z<-qnorm(1-0.05/2)

dat$beta<-with(dat,ifelse(!is.na(diff_beta),diff_beta,
                          ifelse(is.na(diff_beta),group1_beta-group2_beta,NA)))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_lo), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_lo), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_lo), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_lo),(group1_lo-group1_beta)/-z, NA)))))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_sd), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_sd), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_sd), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_sd),group1_sd/sqrt(group1_n), NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_lo), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_lo), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_lo), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_lo),(group2_lo-group2_beta)/-z, NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_sd), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_sd), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_sd), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_sd),group2_sd/sqrt(group2_n), NA)))))
dat$se<-with(dat,ifelse(!is.na(diff_se),diff_se,
                        ifelse(is.na(diff_se),sqrt(group1_se^2 + group2_se^2),NA)))
dat$n<-with(dat,ifelse(!is.na(diff_n),diff_n,
                       ifelse(is.na(diff_n),as.numeric(dat$group1_n)+as.numeric(dat$group2_n),NA)))

meta<-metagen(TE = dat$beta,
              seTE = dat$se,
              studlab = dat$author,
              data = dat,
              sm = "MD",
              method.tau = "REML",
              hakn = TRUE,
              prediction = FALSE,
              title = c("BW"))

coef_fixed<-ic_guapa(guapa(meta$TE.fixed),guapa(meta$lower.fixed),guapa(meta$upper.fixed))
pval_fixed<-round(meta$pval.fixed,5)
beta_fixed<-round(meta$TE.fixed,5)
ic95lo_fixed<-round(meta$lower.fixed,5)
ic95hi_fixed<-round(meta$upper.fixed,5)

coef_random<-ic_guapa(guapa(meta$TE.random),guapa(meta$lower.random),guapa(meta$upper.random))
pval_random<-round(meta$pval.random,5)
beta_random<-round(meta$TE.random,5)
ic95lo_random<-round(meta$lower.random,5)
ic95hi_random<-round(meta$upper.random,5)

i2<-guapa(meta$I2)
suma<-sum(as.numeric(dat$n))

tab<-NULL
tab<-rbind(tab,cbind(coef_fixed,pval_fixed,beta_fixed,ic95lo_fixed,ic95hi_fixed,
                     coef_random,pval_random,beta_random,ic95lo_random,ic95hi_random,i2,suma))

rownames(tab)<-c("bw")
write.table(tab,file="./",sep=";",col.names=NA)

jpeg(filename = "./", 
     width = 14000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 1.2, mar = c(6, 6, 2, 0), bty = "n", lheight = 0.9)
forest(meta, xlim=c(-600, 600), pch=10, col.diamond="#257622", col.diamond.lines = "#257622", col.random = "#257622", col.diamond.common = "gray35", col.diamond.lines.common = "gray35", col.common = "gray35",  col.square = "#38b334", col.square.lines = "#38b334", col.study = "#2f942b", col.lines = "gray5")
dev.off()

jpeg(filename = "./",
     width = 16000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 0.9, mar = c(6, 6, 2, 2), bty = "o", lheight = 0.1)
funnel(meta_analysis, main = "Funnel Plot of Meta-Analysis", labels = TRUE, cex = 0.5)
text(x = meta_analysis$TE, y = meta_analysis$seTE, labels =  dat$author , pos = 3, cex = 0.5, srt = 45, col="black")
dev.off()

meta$n.e <- dat$group1_n  
meta$n.c <- dat$group2_n  

egger_test <- metabias(meta, method.bias = "Pustejovsky")
print(egger_test)

egger_test <- metabias(meta, method.bias = "linreg")
print(egger_test)



#####SMALL######
setwd("")

dat<-read.csv2("./",header=TRUE,sep=";",dec=".")
z<-qnorm(1-0.05/2)

dat$beta<-with(dat,ifelse(!is.na(diff_beta),diff_beta,
                          ifelse(is.na(diff_beta),group1_beta-group2_beta,NA)))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_lo), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_lo), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_lo), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_lo),(group1_lo-group1_beta)/-z, NA)))))
dat$group1_se<-with(dat, ifelse(!is.na(group1_se) & is.na(group1_sd), group1_se,
                                ifelse(!is.na(group1_se) & !is.na(group1_sd), group1_se,
                                       ifelse(is.na(group1_se) & is.na(group1_sd), NA,
                                              ifelse(is.na(group1_se) & !is.na(group1_sd),group1_sd/sqrt(group1_n), NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_lo), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_lo), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_lo), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_lo),(group2_lo-group2_beta)/-z, NA)))))
dat$group2_se<-with(dat, ifelse(!is.na(group2_se) & is.na(group2_sd), group2_se,
                                ifelse(!is.na(group2_se) & !is.na(group2_sd), group2_se,
                                       ifelse(is.na(group2_se) & is.na(group2_sd), NA,
                                              ifelse(is.na(group2_se) & !is.na(group2_sd),group2_sd/sqrt(group2_n), NA)))))
dat$se<-with(dat,ifelse(!is.na(diff_se),diff_se,
                        ifelse(is.na(diff_se),sqrt(group1_se^2 + group2_se^2),NA)))
dat$n<-with(dat,ifelse(!is.na(diff_n),diff_n,
                       ifelse(is.na(diff_n),as.numeric(dat$group1_n)+as.numeric(dat$group2_n),NA)))

meta<-metagen(TE = dat$beta,
              seTE = dat$se,
              studlab = dat$author,
              data = dat,
              sm = "MD",
              method.tau = "REML",
              hakn = TRUE,
              prediction = FALSE,
              title = c("BW"))

coef_fixed<-ic_guapa(guapa(meta$TE.fixed),guapa(meta$lower.fixed),guapa(meta$upper.fixed))
pval_fixed<-round(meta$pval.fixed,5)
beta_fixed<-round(meta$TE.fixed,5)
ic95lo_fixed<-round(meta$lower.fixed,5)
ic95hi_fixed<-round(meta$upper.fixed,5)

coef_random<-ic_guapa(guapa(meta$TE.random),guapa(meta$lower.random),guapa(meta$upper.random))
pval_random<-round(meta$pval.random,5)
beta_random<-round(meta$TE.random,5)
ic95lo_random<-round(meta$lower.random,5)
ic95hi_random<-round(meta$upper.random,5)

i2<-guapa(meta$I2)
suma<-sum(as.numeric(dat$n))

tab<-NULL
tab<-rbind(tab,cbind(coef_fixed,pval_fixed,beta_fixed,ic95lo_fixed,ic95hi_fixed,
                     coef_random,pval_random,beta_random,ic95lo_random,ic95hi_random,i2,suma))

rownames(tab)<-c("bw")
write.table(tab,file="./",sep=";",col.names=NA)

jpeg(filename = "./", 
     width = 14000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 1.2, mar = c(6, 6, 2, 0), bty = "n", lheight = 0.9)
forest(meta, xlim=c(-600, 600), pch=10, col.diamond="#257622", col.diamond.lines = "#257622", col.random = "#257622", col.diamond.common = "gray35", col.diamond.lines.common = "gray35", col.common = "gray35",  col.square = "#38b334", col.square.lines = "#38b334", col.study = "#2f942b", col.lines = "gray5")
dev.off()

jpeg(filename = "./",
     width = 16000, height = 7000, units = "px", res = 1200)
par(las = 1, cex = 0.9, mar = c(6, 6, 2, 2), bty = "o", lheight = 0.1)
funnel(meta_analysis, main = "Funnel Plot of Meta-Analysis", labels = TRUE, cex = 0.5)
text(x = meta_analysis$TE, y = meta_analysis$seTE, labels =  dat$author , pos = 3, cex = 0.5, srt = 45, col="black")
dev.off()

meta$n.e <- dat$group1_n  
meta$n.c <- dat$group2_n  

egger_test <- metabias(meta, method.bias = "Pustejovsky")
print(egger_test)

egger_test <- metabias(meta, method.bias = "linreg")
print(egger_test)

####Repeat for sensitivity analysis####