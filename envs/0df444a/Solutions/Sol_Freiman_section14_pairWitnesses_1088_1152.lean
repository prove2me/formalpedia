-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_1088_1152
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:42:37.311703+00:00
-- url     : https://prove2.me/submissions/f727d959-6337-4c56-87ee-78324f4b0060

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_1088_1152
private theorem valid1088 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1085) (section14Witness section14Catalog 1089)) := by
  let l : CertBound := ⟨true,true,⟨⟨(68287/280379),(67736/280379),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (70068809792562599897900 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1089 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1086) (section14Witness section14Catalog 1090)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(35255/336938),0,0,(1145/336938)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (810113973957577090548417 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1090 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1087) (section14Witness section14Catalog 1091)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(265/1394),0,0,(-5/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (739405926736834253823276 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1091 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1088) (section14Witness section14Catalog 1092)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1805/23782),(12589/71346),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (651691942850884368148435 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1092 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1089) (section14Witness section14Catalog 1093)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(49357/240670),0,0,(1603/240670)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (641862537341731541245051 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1093 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1090) (section14Witness section14Catalog 1094)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-8035/56212),(3194/14053),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (621026962620605889072016 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1094 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1091) (section14Witness section14Catalog 1095)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1063/361537),(165244/1084611),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (606375611515395894298546 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1095 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1092) (section14Witness section14Catalog 1096)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5415/6253),(12589/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5453229660614925466912289 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1096 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1093) (section14Witness section14Catalog 1097)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3189/75517),(165244/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4652256851904432565228407 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1097 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1094) (section14Witness section14Catalog 1098)) := by
  let l : CertBound := ⟨true,false,⟨⟨(32140/30251),(51104/30251),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4892967997052628479701410 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1098 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1095) (section14Witness section14Catalog 1099)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7051/1414),0,0,(-229/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5295362164851135625084020 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1099 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1096) (section14Witness section14Catalog 1100)) := by
  let l : CertBound := ⟨true,true,⟨⟨(49357/5050),0,0,(-1603/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11563246506121738698004650 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1100 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1097) (section14Witness section14Catalog 1101)) := by
  let l : CertBound := ⟨true,true,⟨⟨(53/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7671389399686603411317878 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1101 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1098) (section14Witness section14Catalog 1102)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(2386467/10200659),0,0,(-207422/10200659)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (740576993910960541861698 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1102 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1099) (section14Witness section14Catalog 1103)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1269/13025),0,0,(1628/91175)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(77/250),0,0,(-1/1750)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (686671167939898322244482 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1103 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1100) (section14Witness section14Catalog 1104)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(79515/734834),0,0,(14555/734834)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (658253659661531779993604 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1104 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1101) (section14Witness section14Catalog 1105)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1667875/19069739),(8479231/38139478),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (519747420986645556276938 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1105 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1102) (section14Witness section14Catalog 1106)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(16705269/36430925),0,0,(-1451954/36430925)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (550252703391095009401529 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1106 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1103) (section14Witness section14Catalog 1107)) := by
  let l : CertBound := ⟨true,false,⟨⟨(29680492/32011681),(69595496/32011681),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5894641222071287047192894 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1107 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1104) (section14Witness section14Catalog 1108)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1088755/291718),0,0,(1820975/6126078)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6497925498588944826855996 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1108 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1105) (section14Witness section14Catalog 1109)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1524257/208370),0,0,(72839/125022)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13849291256894150578307011 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1109 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1106) (section14Witness section14Catalog 1110)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2131/134),0,0,(-715/402)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10491123774526563215415882 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1110 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1107) (section14Witness section14Catalog 1111)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32777/2278),0,0,(-10955/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(411/1126),0,0,(-1/1126)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9430486294067327214649387 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1111 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1108) (section14Witness section14Catalog 1112)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(2290185/20401318),0,0,(-21445/2914474)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (827738120940205070310186 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1112 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1109) (section14Witness section14Catalog 1113)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2421/26050),0,0,(61/26050)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(77/250),0,0,(-1/1750)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (792484998034262898019594 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1113 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1110) (section14Witness section14Catalog 1114)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(76041/734834),0,0,(1859/734834)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (775709816197261433710446 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1114 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1111) (section14Witness section14Catalog 1115)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1239849/32271866),(3633695/32271866),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (717373612469173265190642 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1115 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1112) (section14Witness section14Catalog 1116)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(3206259/14572370),0,0,(-210161/14572370)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (721088512368414285160565 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1116 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1113) (section14Witness section14Catalog 1117)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-420355/5867612),(411931/2933806),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (696223181618408042602043 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1117 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1114) (section14Witness section14Catalog 1118)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(11121189/564038882),(52154359/564038882),0,0⟩,⟨(8222/27073),(1/27073),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (684469899247688403461638 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1118 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1115) (section14Witness section14Catalog 1119)) := by
  let l : CertBound := ⟨true,false,⟨⟨(17254936/32011681),(40126628/32011681),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2929664676336619988957478 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1119 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1116) (section14Witness section14Catalog 1120)) := by
  let l : CertBound := ⟨true,false,⟨⟨(618025/291718),0,0,(1138175/6126078)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3321277033370773322672543 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1120 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1117) (section14Witness section14Catalog 1121)) := by
  let l : CertBound := ⟨true,true,⟨⟨(173047/41674),0,0,(45527/125022)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7623060265066534430107444 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1121 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1118) (section14Witness section14Catalog 1122)) := by
  let l : CertBound := ⟨true,true,⟨⟨(20633/2278),0,0,(-6731/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(457/1258),0,0,(1/1258)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5693928564743046257820632 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1122 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1119) (section14Witness section14Catalog 1123)) := by
  let l : CertBound := ⟨true,true,⟨⟨(18011/2278),0,0,(-5819/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4886287180540141780172751 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1123 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1120) (section14Witness section14Catalog 1124)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1825245/3990182),0,0,(-1235165/27931274)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (575709668343887121635018 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1124 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1121) (section14Witness section14Catalog 1125)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(47115/267794),0,0,(8555/267794)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (481105129976100497394599 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1125 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1122) (section14Witness section14Catalog 1126)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(4023/19823),0,0,(728/19823)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (411066355614190297034923 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1126 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1123) (section14Witness section14Catalog 1127)) := by
  let l : CertBound := ⟨true,true,⟨⟨(10515/21074),0,0,(1645/21074)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(4023/19823),0,0,(728/19823)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (663325661383852477662566 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1127 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1124) (section14Witness section14Catalog 1128)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-920050/5656079),(4620961/11312158),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (167277533860030492883241 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1128 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1125) (section14Witness section14Catalog 1129)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2555343/2850130),0,0,(-247033/2850130)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (231232438703818933022747 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1129 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1126) (section14Witness section14Catalog 1130)) := by
  let l : CertBound := ⟨true,true,⟨⟨(10515/21074),0,0,(1645/21074)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-920050/5656079),(4620961/11312158),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (426080027384303799835350 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1130 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1127) (section14Witness section14Catalog 1131)) := by
  let l : CertBound := ⟨true,false,⟨⟨(17132/10153),(135985/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13007399874042732799424807 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1131 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1128) (section14Witness section14Catalog 1132)) := by
  let l : CertBound := ⟨true,false,⟨⟨(26141/3290),0,0,(3841/9870)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13470715095725533341348516 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1132 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1129) (section14Witness section14Catalog 1133)) := by
  let l : CertBound := ⟨true,true,⟨⟨(182987/11750),0,0,(26887/35250)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (27509897016845659932000873 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1133 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1130) (section14Witness section14Catalog 1134)) := by
  let l : CertBound := ⟨true,true,⟨⟨(29513/2050),0,0,(-299/6150)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (20148027479723174815514050 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1134 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1131) (section14Witness section14Catalog 1135)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2853183/3188042),(50246137/9564126),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(11574/32101),(-1/32101),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11180108527551324237877462 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1135 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1132) (section14Witness section14Catalog 1136)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5924164/2812381),(10565558/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11794685468296613311968041 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1136 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1133) (section14Witness section14Catalog 1137)) := by
  let l : CertBound := ⟨true,true,⟨⟨(13369/1025),0,0,(-112/3075)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(411/1126),0,0,(-1/1126)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (18208849402218684611943185 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1137 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1134) (section14Witness section14Catalog 1138)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(871245/3990182),0,0,(-464435/27931274)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (733466849465265274971507 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1138 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1135) (section14Witness section14Catalog 1139)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(45801/267794),0,0,(899/267794)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (671379435256508015694288 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1139 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1136) (section14Witness section14Catalog 1140)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7875/39646),0,0,(139/39646)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (630211134675202918016793 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1140 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1137) (section14Witness section14Catalog 1141)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-685269/9571826),(1980095/9571826),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (529093734161818909037133 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1141 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1138) (section14Witness section14Catalog 1142)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1219743/2850130),0,0,(-92887/2850130)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (540436513701720113562267 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1142 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1139) (section14Witness section14Catalog 1143)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-231205/1740332),(112268/435083),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (490371293235530225707312 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1143 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1140) (section14Witness section14Catalog 1144)) := by
  let l : CertBound := ⟨true,true,⟨⟨(12585013/31555450),0,0,(1965467/31555450)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(871245/3990182),0,0,(-464435/27931274)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (744143408813596603333355 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1144 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1141) (section14Witness section14Catalog 1145)) := by
  let l : CertBound := ⟨true,true,⟨⟨(12585013/31555450),0,0,(1965467/31555450)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(45801/267794),0,0,(899/267794)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (683772191581362011525613 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1145 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1142) (section14Witness section14Catalog 1146)) := by
  let l : CertBound := ⟨true,true,⟨⟨(12585013/31555450),0,0,(1965467/31555450)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-685269/9571826),(1980095/9571826),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (545384169183912571392014 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1146 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1143) (section14Witness section14Catalog 1147)) := by
  let l : CertBound := ⟨true,true,⟨⟨(12585013/31555450),0,0,(1965467/31555450)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1219743/2850130),0,0,(-92887/2850130)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (556427069168600412787692 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1147 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1144) (section14Witness section14Catalog 1148)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(6632997/171175763),(28768888/171175763),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (468095129015073503679357 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1148 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1145) (section14Witness section14Catalog 1149)) := by
  let l : CertBound := ⟨true,false,⟨⟨(767/781),(78400/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7055566369330935954852324 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1149 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1146) (section14Witness section14Catalog 1150)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1475/329),0,0,(256/987)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7404149076715953841185330 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1150 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1147) (section14Witness section14Catalog 1151)) := by
  let l : CertBound := ⟨true,true,⟨⟨(413/47),0,0,(1792/3525)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (15619427619586884111681029 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1151 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1148) (section14Witness section14Catalog 1152)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1697/205),0,0,(4/615)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(457/1258),0,0,(1/1258)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11377249569542315454409129 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 1088).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 1088).take 64 = [⟨1085,[3,5,6],1089⟩,⟨1086,[3,5,7,8,9,11,12,15],1090⟩,⟨1087,[3,5,7,8,9,11,12,15],1091⟩,⟨1088,[3,5,7,8,9,11,12,15],1092⟩,⟨1089,[3,5,7,8,9,11,12,15],1093⟩,⟨1090,[3,5,7,8,9,11,12,15],1094⟩,⟨1091,[3,5,7,8,9,11,12,15],1095⟩,⟨1092,[3,7,11,15],1096⟩,⟨1093,[3,7,11,15],1097⟩,⟨1094,[3,7,11,15],1098⟩,⟨1095,[3,7,11,15],1099⟩,⟨1096,[3,7,11,15],1100⟩,⟨1097,[3,7,11,15],1101⟩,⟨1098,[3,5,7,8,9,11,12,15],1102⟩,⟨1099,[3,5,7,8,9,11,12,15],1103⟩,⟨1100,[3,5,7,8,9,11,12,15],1104⟩,⟨1101,[3,5,7,8,9,11,12,15],1105⟩,⟨1102,[3,5,7,8,9,11,12,15],1106⟩,⟨1103,[3,7,11,15],1107⟩,⟨1104,[3,7,11,15],1108⟩,⟨1105,[3,7,11,15],1109⟩,⟨1106,[3,7,11,15],1110⟩,⟨1107,[3,7,11,15],1111⟩,⟨1108,[3,5,7,8,9,11,12,15],1112⟩,⟨1109,[3,5,7,8,9,11,12,15],1113⟩,⟨1110,[3,5,7,8,9,11,12,15],1114⟩,⟨1111,[3,5,7,8,9,11,12,15],1115⟩,⟨1112,[3,5,7,8,9,11,12,15],1116⟩,⟨1113,[3,5,7,8,9,11,12,15],1117⟩,⟨1114,[3,5,7,8,9,11,12,15],1118⟩,⟨1115,[3,7,11,15],1119⟩,⟨1116,[3,7,11,15],1120⟩,⟨1117,[3,7,11,15],1121⟩,⟨1118,[3,7,11,15],1122⟩,⟨1119,[3,7,11,15],1123⟩,⟨1120,[3,5,7,8,9,11,12,15],1124⟩,⟨1121,[3,5,7,8,9,11,12,15],1125⟩,⟨1122,[3,5,7,8,9,11,12,15],1126⟩,⟨1123,[3,5,7,8,9,11,12,15],1127⟩,⟨1124,[3,5,7,8,9,11,12,15],1128⟩,⟨1125,[3,5,7,8,9,11,12,15],1129⟩,⟨1126,[3,5,7,8,9,11,12,15],1130⟩,⟨1127,[3,7,11,15],1131⟩,⟨1128,[3,7,11,15],1132⟩,⟨1129,[3,7,11,15],1133⟩,⟨1130,[3,7,11,15],1134⟩,⟨1131,[3,7,11,15],1135⟩,⟨1132,[3,7,11,15],1136⟩,⟨1133,[3,7,11,15],1137⟩,⟨1134,[3,5,7,8,9,11,12,15],1138⟩,⟨1135,[3,5,7,8,9,11,12,15],1139⟩,⟨1136,[3,5,7,8,9,11,12,15],1140⟩,⟨1137,[3,5,7,8,9,11,12,15],1141⟩,⟨1138,[3,5,7,8,9,11,12,15],1142⟩,⟨1139,[3,5,7,8,9,11,12,15],1143⟩,⟨1140,[3,5,7,8,9,11,12,15],1144⟩,⟨1141,[3,5,7,8,9,11,12,15],1145⟩,⟨1142,[3,5,7,8,9,11,12,15],1146⟩,⟨1143,[3,5,7,8,9,11,12,15],1147⟩,⟨1144,[3,5,7,8,9,11,12,15],1148⟩,⟨1145,[3,7,11,15],1149⟩,⟨1146,[3,7,11,15],1150⟩,⟨1147,[3,7,11,15],1151⟩,⟨1148,[3,7,11,15],1152⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid1088
  · exact valid1089
  · exact valid1090
  · exact valid1091
  · exact valid1092
  · exact valid1093
  · exact valid1094
  · exact valid1095
  · exact valid1096
  · exact valid1097
  · exact valid1098
  · exact valid1099
  · exact valid1100
  · exact valid1101
  · exact valid1102
  · exact valid1103
  · exact valid1104
  · exact valid1105
  · exact valid1106
  · exact valid1107
  · exact valid1108
  · exact valid1109
  · exact valid1110
  · exact valid1111
  · exact valid1112
  · exact valid1113
  · exact valid1114
  · exact valid1115
  · exact valid1116
  · exact valid1117
  · exact valid1118
  · exact valid1119
  · exact valid1120
  · exact valid1121
  · exact valid1122
  · exact valid1123
  · exact valid1124
  · exact valid1125
  · exact valid1126
  · exact valid1127
  · exact valid1128
  · exact valid1129
  · exact valid1130
  · exact valid1131
  · exact valid1132
  · exact valid1133
  · exact valid1134
  · exact valid1135
  · exact valid1136
  · exact valid1137
  · exact valid1138
  · exact valid1139
  · exact valid1140
  · exact valid1141
  · exact valid1142
  · exact valid1143
  · exact valid1144
  · exact valid1145
  · exact valid1146
  · exact valid1147
  · exact valid1148
  · exact valid1149
  · exact valid1150
  · exact valid1151
end Section14Numerical_1088_1152

#print axioms solution
