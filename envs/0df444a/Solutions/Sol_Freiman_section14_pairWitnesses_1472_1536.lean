-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_1472_1536
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:57:18.044319+00:00
-- url     : https://prove2.me/submissions/2cb3574e-20e8-4ff8-b337-52111962a017

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_1472_1536
private theorem valid1472 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1468) (section14Witness section14Catalog 1473)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-12696/2146969),(66601/2146969),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1015635135085371344376214 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1473 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1469) (section14Witness section14Catalog 1474)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1064/6539),(2138/6539),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (494300184336852464529359 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1474 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1470) (section14Witness section14Catalog 1475)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (485598643694431418456514 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1475 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1471) (section14Witness section14Catalog 1476)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2061822057728612827670511 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1476 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1472) (section14Witness section14Catalog 1477)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1185715873576989208972681 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1477 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1473) (section14Witness section14Catalog 1478)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (696183511884026249351820 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1478 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1474) (section14Witness section14Catalog 1479)) := by
  let l : CertBound := ⟨true,true,⟨⟨(566529/38701),(462677/38701),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(71/229),(-1/229),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (61271254862036785912526134 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1479 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1475) (section14Witness section14Catalog 1480)) := by
  let l : CertBound := ⟨true,true,⟨⟨(4230171/467389),(5763416/467389),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(71/229),(-1/229),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (52532233610123687123351091 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1480 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1476) (section14Witness section14Catalog 1481)) := by
  let l : CertBound := ⟨true,true,⟨⟨(448644/30251),(354923/30251),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (60929277256651702742988414 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1481 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1477) (section14Witness section14Catalog 1482)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (600726480551508022304612 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1482 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1478) (section14Witness section14Catalog 1483)) := by
  let l : CertBound := ⟨true,true,⟨⟨(6428184/32011681),(13034852/32011681),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (376579655171270780815054 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1483 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1479) (section14Witness section14Catalog 1484)) := by
  let l : CertBound := ⟨true,false,⟨⟨(255545/291718),0,0,(-10715/2042026)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (258988745811498013274948 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1484 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1480) (section14Witness section14Catalog 1485)) := by
  let l : CertBound := ⟨true,true,⟨⟨(357763/208370),0,0,(-2143/208370)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1790443932204416919480565 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1485 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1481) (section14Witness section14Catalog 1486)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1705/2278),0,0,(215/2278)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (924391395737209178396755 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1486 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1482) (section14Witness section14Catalog 1487)) := by
  let l : CertBound := ⟨true,true,⟨⟨(17565240/9925019),(12402183/9925019),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5799504050654290139574013 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1487 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1483) (section14Witness section14Catalog 1488)) := by
  let l : CertBound := ⟨true,true,⟨⟨(309779799/239727382),(289606167/239727382),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4826806162250525920576778 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1488 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1484) (section14Witness section14Catalog 1489)) := by
  let l : CertBound := ⟨true,true,⟨⟨(713247900/349053133),(307038560/349053133),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5150198546427849264043393 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1489 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1485) (section14Witness section14Catalog 1490)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3779/10153),(8480/10153),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2063517572475878552013880 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1490 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1486) (section14Witness section14Catalog 1491)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3263/1645),0,0,(-128/1645)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1721192973264113133880855 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1491 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1487) (section14Witness section14Catalog 1492)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22841/5875),0,0,(-896/5875)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4476623065470124175519891 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1492 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1488) (section14Witness section14Catalog 1493)) := by
  let l : CertBound := ⟨true,true,⟨⟨(241/205),0,0,(44/205)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2653362275518531489921199 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1493 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1489) (section14Witness section14Catalog 1494)) := by
  let l : CertBound := ⟨true,true,⟨⟨(13088/122617),(320101/367851),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1702020922348182006933618 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1494 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1490) (section14Witness section14Catalog 1495)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1732493/1187770),0,0,(66717/1187770)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1885210486889428566804527 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1495 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1491) (section14Witness section14Catalog 1496)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1238838/2812381),(1985156/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1788407743361199005936412 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1496 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1492) (section14Witness section14Catalog 1497)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3631/20306),(9205/20306),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (534533062513059508442915 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1497 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1493) (section14Witness section14Catalog 1498)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3211/3290),0,0,(-7/470)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (407283791741791209938454 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1498 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1494) (section14Witness section14Catalog 1499)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22477/11750),0,0,(-343/11750)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2014987367637946431827059 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1499 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1495) (section14Witness section14Catalog 1500)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2317/2050),0,0,(53/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1064997502722361885897872 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1500 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1496) (section14Witness section14Catalog 1501)) := by
  let l : CertBound := ⟨true,true,⟨⟨(618801/2812381),(1073927/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (358228328143859299661394 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1501 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1497) (section14Witness section14Catalog 1502)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(11/210)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (867632393829951501286452 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1502 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1498) (section14Witness section14Catalog 1503)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1981/5291),(1597/5291),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (847702725509324151884596 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1503 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1499) (section14Witness section14Catalog 1504)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-829225/2042326),(654139/2042326),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (846874878051255235201151 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1504 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1500) (section14Witness section14Catalog 1505)) := by
  let l : CertBound := ⟨true,true,⟨⟨(17717/14485),0,0,(-1134/14485)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1246597064903633359448262 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1505 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1501) (section14Witness section14Catalog 1506)) := by
  let l : CertBound := ⟨true,true,⟨⟨(17717/14485),0,0,(-1134/14485)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(11/210)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1173898688726939579073671 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1506 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1502) (section14Witness section14Catalog 1507)) := by
  let l : CertBound := ⟨true,true,⟨⟨(17717/14485),0,0,(-1134/14485)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1981/5291),(1597/5291),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1147535635348094744683076 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1507 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1503) (section14Witness section14Catalog 1508)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-39981/112739),(32838/112739),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (844618391374505253570572 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1508 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1504) (section14Witness section14Catalog 1509)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2049/6887),(2368/6887),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (539356527940966654575312 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1509 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1505) (section14Witness section14Catalog 1510)) := by
  let l : CertBound := ⟨true,true,⟨⟨(76565/242209),(79485/242209),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (522417922316151062169285 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1510 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1506) (section14Witness section14Catalog 1511)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7565/68302),(13814/34151),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (391159140073431059396309 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1511 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1507) (section14Witness section14Catalog 1512)) := by
  let l : CertBound := ⟨true,true,⟨⟨(365445/2402114),(2710495/7206342),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (371791865861350345378347 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1512 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1508) (section14Witness section14Catalog 1513)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1678848672161360916674068 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1513 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1509) (section14Witness section14Catalog 1514)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (929872274528358581097805 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1514 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1510) (section14Witness section14Catalog 1515)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-54/407),(85/407),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (657279305090803095389856 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1515 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1511) (section14Witness section14Catalog 1516)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1455/5291),(3191/10582),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (615243694472651356058785 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1516 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1512) (section14Witness section14Catalog 1517)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1/5291),(809/5291),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (579070894603374509042745 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1517 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1513) (section14Witness section14Catalog 1518)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(25/119),0,0,(-4/119)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (412632848580570864548957 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1518 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1514) (section14Witness section14Catalog 1519)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/5),0,0,(2/35)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (384288250761778287275664 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1519 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1515) (section14Witness section14Catalog 1520)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/34),0,0,(3/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (373813191415035603387485 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1520 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1516) (section14Witness section14Catalog 1521)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(3/407),(2/37),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (322677301932521014490301 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1521 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1517) (section14Witness section14Catalog 1522)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(133/21164),(324/5291),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (304346442077262182306663 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1522 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1518) (section14Witness section14Catalog 1523)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(17/481),(249/5291),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(101/143),(-1/429),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (294132941936669996068922 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1523 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1519) (section14Witness section14Catalog 1524)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7/17),0,0,(-28/425)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (324845687703528268453366 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1524 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1520) (section14Witness section14Catalog 1525)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(10755/428029),0,0,(-1340/428029)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (391874612301390239825389 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1525 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1521) (section14Witness section14Catalog 1526)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-99/3901),0,0,(32/3901)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (385891493125649228596998 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1526 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1522) (section14Witness section14Catalog 1527)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-59/2050),0,0,(19/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (387210937488342835225422 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1527 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1523) (section14Witness section14Catalog 1528)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(76/46079),(449/46079),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (376051209840596573464877 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1528 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1524) (section14Witness section14Catalog 1529)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(163/108914),(7211/653484),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (372688581169633829553451 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1529 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1525) (section14Witness section14Catalog 1530)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9875/1620553),(14217/1620553),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (371060304587468779435952 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1530 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1526) (section14Witness section14Catalog 1531)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(15057/305735),0,0,(-1876/305735)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (374989301857175114156366 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1531 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1527) (section14Witness section14Catalog 1532)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(85/938),0,0,(-5/938)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (307407950339683033837402 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1532 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1528) (section14Witness section14Catalog 1533)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/34),0,0,(3/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (259344771566904967680087 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1533 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1529) (section14Witness section14Catalog 1534)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(3/407),(2/37),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (233358039695766881332652 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1534 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1530) (section14Witness section14Catalog 1535)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/52),(7/52),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(119/670),0,0,(-7/670)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (203733788401717690913003 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1535 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1531) (section14Witness section14Catalog 1536)) := by
  let l : CertBound := ⟨true,false,⟨⟨(421/5564),(171/1391),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(1/2)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (80557244439626874657192 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 1472).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 1472).take 64 = [⟨1468,[5,8,9,12],1473⟩,⟨1469,[5,8,9,12],1474⟩,⟨1470,[5,8,9,12],1475⟩,⟨1471,[5,8,9,12],1476⟩,⟨1472,[5,8,9,12],1477⟩,⟨1473,[5,9],1478⟩,⟨1474,[5,8,9,12],1479⟩,⟨1475,[5,8,9,12],1480⟩,⟨1476,[5,8,9,12],1481⟩,⟨1477,[5,9],1482⟩,⟨1478,[5,8,9,12],1483⟩,⟨1479,[5,8,9,12],1484⟩,⟨1480,[5,8,9,12],1485⟩,⟨1481,[5,8,9,12],1486⟩,⟨1482,[5,8,9,12],1487⟩,⟨1483,[5,8,9,12],1488⟩,⟨1484,[5,8,9,12],1489⟩,⟨1485,[5,8,9,12],1490⟩,⟨1486,[5,8,9,12],1491⟩,⟨1487,[5,8,9,12],1492⟩,⟨1488,[5,8,9,12],1493⟩,⟨1489,[5,8,9,12],1494⟩,⟨1490,[5,8,9,12],1495⟩,⟨1491,[5,8,9,12],1496⟩,⟨1492,[5,8,9,12],1497⟩,⟨1493,[5,8,9,12],1498⟩,⟨1494,[5,8,9,12],1499⟩,⟨1495,[5,8,9,12],1500⟩,⟨1496,[5,8,9,12],1501⟩,⟨1497,[5,8,9,12],1502⟩,⟨1498,[5,8,9,12],1503⟩,⟨1499,[5,8,9,12],1504⟩,⟨1500,[5,8,9,12],1505⟩,⟨1501,[5,8,9,12],1506⟩,⟨1502,[5,8,9,12],1507⟩,⟨1503,[5,8,9,12],1508⟩,⟨1504,[5,8,9,12],1509⟩,⟨1505,[5,8,9,12],1510⟩,⟨1506,[5,8,9,12],1511⟩,⟨1507,[5,8,9,12],1512⟩,⟨1508,[5,8,9,12],1513⟩,⟨1509,[5,8,9,12],1514⟩,⟨1510,[5,8,9,12],1515⟩,⟨1511,[5,8,9,12],1516⟩,⟨1512,[5,8,9,12],1517⟩,⟨1513,[6],1518⟩,⟨1514,[6],1519⟩,⟨1515,[6],1520⟩,⟨1516,[6],1521⟩,⟨1517,[6],1522⟩,⟨1518,[6],1523⟩,⟨1519,[6],1524⟩,⟨1520,[6],1525⟩,⟨1521,[6],1526⟩,⟨1522,[6],1527⟩,⟨1523,[6],1528⟩,⟨1524,[6],1529⟩,⟨1525,[6],1530⟩,⟨1526,[6],1531⟩,⟨1527,[6],1532⟩,⟨1528,[6],1533⟩,⟨1529,[6],1534⟩,⟨1530,[6],1535⟩,⟨1531,[6,10],1536⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid1472
  · exact valid1473
  · exact valid1474
  · exact valid1475
  · exact valid1476
  · exact valid1477
  · exact valid1478
  · exact valid1479
  · exact valid1480
  · exact valid1481
  · exact valid1482
  · exact valid1483
  · exact valid1484
  · exact valid1485
  · exact valid1486
  · exact valid1487
  · exact valid1488
  · exact valid1489
  · exact valid1490
  · exact valid1491
  · exact valid1492
  · exact valid1493
  · exact valid1494
  · exact valid1495
  · exact valid1496
  · exact valid1497
  · exact valid1498
  · exact valid1499
  · exact valid1500
  · exact valid1501
  · exact valid1502
  · exact valid1503
  · exact valid1504
  · exact valid1505
  · exact valid1506
  · exact valid1507
  · exact valid1508
  · exact valid1509
  · exact valid1510
  · exact valid1511
  · exact valid1512
  · exact valid1513
  · exact valid1514
  · exact valid1515
  · exact valid1516
  · exact valid1517
  · exact valid1518
  · exact valid1519
  · exact valid1520
  · exact valid1521
  · exact valid1522
  · exact valid1523
  · exact valid1524
  · exact valid1525
  · exact valid1526
  · exact valid1527
  · exact valid1528
  · exact valid1529
  · exact valid1530
  · exact valid1531
  · exact valid1532
  · exact valid1533
  · exact valid1534
  · exact valid1535
end Section14Numerical_1472_1536

#print axioms solution
