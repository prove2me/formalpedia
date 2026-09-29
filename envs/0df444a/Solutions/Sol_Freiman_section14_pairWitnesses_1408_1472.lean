-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_1408_1472
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:47:06.371357+00:00
-- url     : https://prove2.me/submissions/fd6df579-6523-4a33-bd5b-8ef0487015fd

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_1408_1472
private theorem valid1408 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1404) (section14Witness section14Catalog 1409)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-12696/2146969),(66601/2146969),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (599221427166265781443550 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1409 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1405) (section14Witness section14Catalog 1410)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/17),0,0,(4/51)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (290399651751225519813517 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1410 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1406) (section14Witness section14Catalog 1411)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-54/407),(85/407),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (213178552312507030982632 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1411 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1407) (section14Witness section14Catalog 1412)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/2),(5/6),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2633522023238931952250350 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1412 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1408) (section14Witness section14Catalog 1413)) := by
  let l : CertBound := ⟨true,false,⟨⟨(18/157),(431/471),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2090450687887494234419588 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1413 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1409) (section14Witness section14Catalog 1414)) := by
  let l : CertBound := ⟨true,false,⟨⟨(65/107),(221/321),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2321622900795486958885392 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1414 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1410) (section14Witness section14Catalog 1415)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3721716313448927498529771 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1415 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1411) (section14Witness section14Catalog 1416)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-1/2),0,0,(59/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3461317344728607340450685 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1416 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1412) (section14Witness section14Catalog 1417)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/50),0,0,(59/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8304714940794035249900867 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1417 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1413) (section14Witness section14Catalog 1418)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4920524313745055158884470 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1418 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1414) (section14Witness section14Catalog 1419)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5415/6253),(12589/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6725483453273381301101345 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1419 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1415) (section14Witness section14Catalog 1420)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3189/75517),(165244/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5768768790983530124589868 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1420 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1416) (section14Witness section14Catalog 1421)) := by
  let l : CertBound := ⟨true,false,⟨⟨(32140/30251),(51104/30251),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6059048772712067783703240 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1421 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1417) (section14Witness section14Catalog 1422)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7051/1414),0,0,(-229/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6571181601474281481930037 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1422 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1418) (section14Witness section14Catalog 1423)) := by
  let l : CertBound := ⟨true,true,⟨⟨(49357/5050),0,0,(-1603/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (14059349054269359187319266 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1423 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1419) (section14Witness section14Catalog 1424)) := by
  let l : CertBound := ⟨true,true,⟨⟨(53/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9431752970990091855443913 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1424 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1420) (section14Witness section14Catalog 1425)) := by
  let l : CertBound := ⟨true,false,⟨⟨(29680492/32011681),(69595496/32011681),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7112261666620210171025453 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1425 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1421) (section14Witness section14Catalog 1426)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1088755/291718),0,0,(1820975/6126078)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7817740951386625870915304 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1426 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1422) (section14Witness section14Catalog 1427)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1524257/208370),0,0,(72839/125022)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (16431895902290086959939349 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1427 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1423) (section14Witness section14Catalog 1428)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2131/134),0,0,(-715/402)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (12495827008629306510918132 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1428 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1424) (section14Witness section14Catalog 1429)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32777/2278),0,0,(-10955/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(411/1126),0,0,(-1/1126)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11259289875447473149403488 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1429 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1425) (section14Witness section14Catalog 1430)) := by
  let l : CertBound := ⟨true,false,⟨⟨(17254936/32011681),(40126628/32011681),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3653122363263098603084133 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1430 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1426) (section14Witness section14Catalog 1431)) := by
  let l : CertBound := ⟨true,false,⟨⟨(618025/291718),0,0,(1138175/6126078)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4112015181797930179104812 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1431 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1427) (section14Witness section14Catalog 1432)) := by
  let l : CertBound := ⟨true,true,⟨⟨(173047/41674),0,0,(45527/125022)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9168673393896243403990785 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1432 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1428) (section14Witness section14Catalog 1433)) := by
  let l : CertBound := ⟨true,true,⟨⟨(20633/2278),0,0,(-6731/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(457/1258),0,0,(1/1258)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6899972524569145366436608 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1433 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1429) (section14Witness section14Catalog 1434)) := by
  let l : CertBound := ⟨true,true,⟨⟨(18011/2278),0,0,(-5819/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5956850982311814836467812 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1434 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1430) (section14Witness section14Catalog 1435)) := by
  let l : CertBound := ⟨true,false,⟨⟨(17132/10153),(135985/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (15447159756212686889447566 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1435 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1431) (section14Witness section14Catalog 1436)) := by
  let l : CertBound := ⟨true,false,⟨⟨(26141/3290),0,0,(3841/9870)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (15987180712438858819905831 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1436 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1432) (section14Witness section14Catalog 1437)) := by
  let l : CertBound := ⟨true,true,⟨⟨(182987/11750),0,0,(26887/35250)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(11835/32926),0,0,(1/32926)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (32437959034252625720128845 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1437 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1433) (section14Witness section14Catalog 1438)) := by
  let l : CertBound := ⟨true,true,⟨⟨(29513/2050),0,0,(-299/6150)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(457/1258),0,0,(-1/1258)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (23809576985241399464641734 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1438 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1434) (section14Witness section14Catalog 1439)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2853183/3188042),(50246137/9564126),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(11574/32101),(-1/32101),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13305966473074764783892446 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1439 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1435) (section14Witness section14Catalog 1440)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5924164/2812381),(10565558/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (14025881014489649414001346 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1440 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1436) (section14Witness section14Catalog 1441)) := by
  let l : CertBound := ⟨true,true,⟨⟨(13369/1025),0,0,(-112/3075)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(665/1858),0,0,(1/1858)⟩,⟨(411/1126),0,0,(-1/1126)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (21548799155998338196964198 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1441 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1437) (section14Witness section14Catalog 1442)) := by
  let l : CertBound := ⟨true,false,⟨⟨(767/781),(78400/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8503354000715590570779668 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1442 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1438) (section14Witness section14Catalog 1443)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1475/329),0,0,(256/987)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8910215704914517661703904 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1443 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1439) (section14Witness section14Catalog 1444)) := by
  let l : CertBound := ⟨true,true,⟨⟨(413/47),0,0,(1792/3525)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7081/19270),0,0,(1/19270)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (18567107619504917050053067 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1444 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1440) (section14Witness section14Catalog 1445)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1697/205),0,0,(4/615)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(457/1258),0,0,(1/1258)⟩,⟨(251/670),0,0,(-1/670)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13578599351209240846507799 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1445 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1441) (section14Witness section14Catalog 1446)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-901248/1594021),(14625521/4782063),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(6760/18301),(-1/18301),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7247022137615108937864148 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1446 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1442) (section14Witness section14Catalog 1447)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3436822/2812381),(6092804/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7676739565082034759965821 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1447 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1443) (section14Witness section14Catalog 1448)) := by
  let l : CertBound := ⟨true,true,⟨⟨(14861/2050),0,0,(97/6150)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11854277278057753438957135 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1448 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1444) (section14Witness section14Catalog 1449)) := by
  let l : CertBound := ⟨true,false,⟨⟨(433/923),(3320/2769),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3429034410160020184060820 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1449 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1445) (section14Witness section14Catalog 1450)) := by
  let l : CertBound := ⟨true,false,⟨⟨(6581/3290),0,0,(1513/9870)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3707136305857580962309262 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1450 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1446) (section14Witness section14Catalog 1451)) := by
  let l : CertBound := ⟨true,true,⟨⟨(46067/11750),0,0,(10591/35250)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(105/262),0,0,(-1/262)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8369071997353321119239569 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1451 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1447) (section14Witness section14Catalog 1452)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7757/2050),0,0,(289/6150)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(105/262),0,0,(-1/262)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6029900497634951529008228 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1452 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1448) (section14Witness section14Catalog 1453)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-89043/289822),(1262909/869466),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2823061635469664810517022 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1453 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1449) (section14Witness section14Catalog 1454)) := by
  let l : CertBound := ⟨true,false,⟨⟨(147986/255671),(258172/255671),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3036982352053393282016783 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1454 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1450) (section14Witness section14Catalog 1455)) := by
  let l : CertBound := ⟨true,true,⟨⟨(77/25),0,0,(4/75)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4842034180575037981584438 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1455 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1451) (section14Witness section14Catalog 1456)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(445/48134),0,0,(2115/336938)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1095954825328384996119540 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1456 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1452) (section14Witness section14Catalog 1457)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-37/1394),0,0,(27/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1054795135238966233491517 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1457 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1453) (section14Witness section14Catalog 1458)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-536/11891),(875/11891),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1003380999726400827205831 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1458 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1454) (section14Witness section14Catalog 1459)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(4361/240670),0,0,(2961/240670)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1012536896551776392557528 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1459 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1455) (section14Witness section14Catalog 1460)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1330/14053),(2979/28106),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (988263209182634390442041 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1460 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1456) (section14Witness section14Catalog 1461)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-4897/361537),(22359/361537),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (979030347098460053865359 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1461 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1457) (section14Witness section14Catalog 1462)) := by
  let l : CertBound := ⟨true,false,⟨⟨(55/169),(121/169),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2316291158325948050759095 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1462 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1458) (section14Witness section14Catalog 1463)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5313/75517),(57277/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(113/179),(1/537),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1899582675350966944053195 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1463 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1459) (section14Witness section14Catalog 1464)) := by
  let l : CertBound := ⟨true,false,⟨⟨(11860/30251),(54616/90753),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2019179304990055796522972 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1464 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1460) (section14Witness section14Catalog 1465)) := by
  let l : CertBound := ⟨true,false,⟨⟨(2697/1414),0,0,(-19/202)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2164565189654667705262142 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1465 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1461) (section14Witness section14Catalog 1466)) := by
  let l : CertBound := ⟨true,true,⟨⟨(18879/5050),0,0,(-931/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5422380887102916185050192 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1466 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1462) (section14Witness section14Catalog 1467)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(139/250),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3357799857313445015560534 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1467 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1463) (section14Witness section14Catalog 1468)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1/235),0,0,(16/4935)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1076009496393925868210874 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1468 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1464) (section14Witness section14Catalog 1469)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/1025),0,0,(28/3075)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1055857675262338245023798 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1469 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1465) (section14Witness section14Catalog 1470)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1043/46079),(1720/46079),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1028238123229200613811805 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1470 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1466) (section14Witness section14Catalog 1471)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(49/5875),0,0,(112/17625)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1034064593523236030009975 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1471 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1467) (section14Witness section14Catalog 1472)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-5195/108914),(2926/54457),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1020527074725086286669224 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 1408).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 1408).take 64 = [⟨1404,[5,6,8,9,10,12],1409⟩,⟨1405,[5,6,7,8,9,10,12],1410⟩,⟨1406,[5,6,8,9,10,12],1411⟩,⟨1407,[5,8],1412⟩,⟨1408,[5,8],1413⟩,⟨1409,[5,8],1414⟩,⟨1410,[5,8,9,12],1415⟩,⟨1411,[5,8],1416⟩,⟨1412,[5,8],1417⟩,⟨1413,[5,8],1418⟩,⟨1414,[5,8,9,12],1419⟩,⟨1415,[5,8,9,12],1420⟩,⟨1416,[5,8,9,12],1421⟩,⟨1417,[5,8,9,12],1422⟩,⟨1418,[5,8,9,12],1423⟩,⟨1419,[5,8,9,12],1424⟩,⟨1420,[5,8,9,12],1425⟩,⟨1421,[5,8,9,12],1426⟩,⟨1422,[5,8,9,12],1427⟩,⟨1423,[5,8,9,12],1428⟩,⟨1424,[5,8,9,12],1429⟩,⟨1425,[5,8,9,12],1430⟩,⟨1426,[5,8,9,12],1431⟩,⟨1427,[5,8,9,12],1432⟩,⟨1428,[5,8,9,12],1433⟩,⟨1429,[5,8,9,12],1434⟩,⟨1430,[5,8,9,12],1435⟩,⟨1431,[5,8,9,12],1436⟩,⟨1432,[5,8,9,12],1437⟩,⟨1433,[5,8,9,12],1438⟩,⟨1434,[5,8,9,12],1439⟩,⟨1435,[5,8,9,12],1440⟩,⟨1436,[5,8,9,12],1441⟩,⟨1437,[5,8,9,12],1442⟩,⟨1438,[5,8,9,12],1443⟩,⟨1439,[5,8,9,12],1444⟩,⟨1440,[5,8,9,12],1445⟩,⟨1441,[5,8,9,12],1446⟩,⟨1442,[5,8,9,12],1447⟩,⟨1443,[5,8,9,12],1448⟩,⟨1444,[5,8,9,12],1449⟩,⟨1445,[5,8,9,12],1450⟩,⟨1446,[5,8,9,12],1451⟩,⟨1447,[5,8,9,12],1452⟩,⟨1448,[5,8,9,12],1453⟩,⟨1449,[5,8,9,12],1454⟩,⟨1450,[5,8,9,12],1455⟩,⟨1451,[5,8,9,12],1456⟩,⟨1452,[5,8,9,12],1457⟩,⟨1453,[5,8,9,12],1458⟩,⟨1454,[5,8,9,12],1459⟩,⟨1455,[5,8,9,12],1460⟩,⟨1456,[5,8,9,12],1461⟩,⟨1457,[5,8,9,12],1462⟩,⟨1458,[5,8,9,12],1463⟩,⟨1459,[5,8,9,12],1464⟩,⟨1460,[5,8,9,12],1465⟩,⟨1461,[5,8,9,12],1466⟩,⟨1462,[5,8,9,12],1467⟩,⟨1463,[5,8,9,12],1468⟩,⟨1464,[5,8,9,12],1469⟩,⟨1465,[5,8,9,12],1470⟩,⟨1466,[5,8,9,12],1471⟩,⟨1467,[5,8,9,12],1472⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid1408
  · exact valid1409
  · exact valid1410
  · exact valid1411
  · exact valid1412
  · exact valid1413
  · exact valid1414
  · exact valid1415
  · exact valid1416
  · exact valid1417
  · exact valid1418
  · exact valid1419
  · exact valid1420
  · exact valid1421
  · exact valid1422
  · exact valid1423
  · exact valid1424
  · exact valid1425
  · exact valid1426
  · exact valid1427
  · exact valid1428
  · exact valid1429
  · exact valid1430
  · exact valid1431
  · exact valid1432
  · exact valid1433
  · exact valid1434
  · exact valid1435
  · exact valid1436
  · exact valid1437
  · exact valid1438
  · exact valid1439
  · exact valid1440
  · exact valid1441
  · exact valid1442
  · exact valid1443
  · exact valid1444
  · exact valid1445
  · exact valid1446
  · exact valid1447
  · exact valid1448
  · exact valid1449
  · exact valid1450
  · exact valid1451
  · exact valid1452
  · exact valid1453
  · exact valid1454
  · exact valid1455
  · exact valid1456
  · exact valid1457
  · exact valid1458
  · exact valid1459
  · exact valid1460
  · exact valid1461
  · exact valid1462
  · exact valid1463
  · exact valid1464
  · exact valid1465
  · exact valid1466
  · exact valid1467
  · exact valid1468
  · exact valid1469
  · exact valid1470
  · exact valid1471
end Section14Numerical_1408_1472

#print axioms solution
