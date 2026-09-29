-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_0384_0512
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:05:56.984429+00:00
-- url     : https://prove2.me/submissions/9a53a8be-28f5-418a-8f64-80e370178cb9

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_384_512
private theorem valid384 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 384) (section14Witness section14Catalog 385)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(69/200),0,0,0⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1093836592701543581413051 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid385 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 385) (section14Witness section14Catalog 386)) := by
  let l : CertBound := ⟨true,false,⟨⟨(161/500),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,-1,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (148056548896928453812895 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid386 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 386) (section14Witness section14Catalog 387)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (811446292774011376838889 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid387 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 387) (section14Witness section14Catalog 388)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (833653007652168919627992 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid388 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 388) (section14Witness section14Catalog 389)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (742862994083343926247741 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid389 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 389) (section14Witness section14Catalog 390)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (686069880666901158964659 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid390 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 390) (section14Witness section14Catalog 391)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (682444754482575963205186 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid391 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 391) (section14Witness section14Catalog 392)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (671891326388064326166132 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid392 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 392) (section14Witness section14Catalog 393)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (452308092374774569054851 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid393 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 393) (section14Witness section14Catalog 394)) := by
  let l : CertBound := ⟨true,false,⟨⟨(18/157),(431/471),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1462408629010614742018188 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid394 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 394) (section14Witness section14Catalog 395)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/2),(5/6),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1858069431761594152255189 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid395 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 395) (section14Witness section14Catalog 396)) := by
  let l : CertBound := ⟨true,false,⟨⟨(65/107),(221/321),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1625524206027570857156683 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid396 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 396) (section14Witness section14Catalog 397)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2894141124744704811110033 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid397 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 397) (section14Witness section14Catalog 398)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-1/2),0,0,(59/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2385870671393623658158959 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid398 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 398) (section14Witness section14Catalog 399)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/50),0,0,(59/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5910642679147105007623660 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid399 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 399) (section14Witness section14Catalog 400)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3396811586002072669724243 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid400 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 400) (section14Witness section14Catalog 401)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(35255/336938),0,0,(1145/336938)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (844214540728519919211918 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid401 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 401) (section14Witness section14Catalog 402)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(265/1394),0,0,(-5/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (772426892321705606520352 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid402 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 402) (section14Witness section14Catalog 403)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1805/23782),(12589/71346),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (682120476232682425379263 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid403 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 403) (section14Witness section14Catalog 404)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(49357/240670),0,0,(1603/240670)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (670264997032853825912982 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid404 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 404) (section14Witness section14Catalog 405)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-8035/56212),(3194/14053),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (650403387538643294429888 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid405 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 405) (section14Witness section14Catalog 406)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1063/361537),(165244/1084611),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (635499774483603119030690 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid406 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 406) (section14Witness section14Catalog 407)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5415/6253),(12589/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5259556838822726546455909 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid407 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 407) (section14Witness section14Catalog 408)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3189/75517),(165244/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4509730889337816537268221 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid408 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 408) (section14Witness section14Catalog 409)) := by
  let l : CertBound := ⟨true,false,⟨⟨(32140/30251),(51104/30251),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4735315737704587928862360 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid409 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 409) (section14Witness section14Catalog 410)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7051/1414),0,0,(-229/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5114457783683174837310178 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid410 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 410) (section14Witness section14Catalog 411)) := by
  let l : CertBound := ⟨true,true,⟨⟨(49357/5050),0,0,(-1603/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10982100575479311711010605 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid411 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 411) (section14Witness section14Catalog 412)) := by
  let l : CertBound := ⟨true,true,⟨⟨(53/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7336090411391814920385284 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid412 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 412) (section14Witness section14Catalog 413)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(527475/4417763),0,0,(2650/4417763)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (802991029024017449917781 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid413 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 413) (section14Witness section14Catalog 414)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(17463/99115),0,0,(-92/99115)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (733486578080441299645989 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid414 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 414) (section14Witness section14Catalog 415)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-312702/4785913),(815035/4785913),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (654272753511026172981329 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid415 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 415) (section14Witness section14Catalog 416)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-689614/5656079),(2436481/11312158),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (624567240689611142938683 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid416 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 416) (section14Witness section14Catalog 417)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(32229/5645497),(832214/5645497),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(4840/16393),(-1/16393),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (610851948005647111749264 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid417 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 417) (section14Witness section14Catalog 418)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(147693/631109),0,0,(742/631109)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (641002558496754020375183 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid418 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 418) (section14Witness section14Catalog 419)) := by
  let l : CertBound := ⟨true,false,⟨⟨(8018/10153),(62695/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5011080151828441526081924 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid419 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 419) (section14Witness section14Catalog 420)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7033/1645),0,0,(-106/4935)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4767316195784958495212821 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid420 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 420) (section14Witness section14Catalog 421)) := by
  let l : CertBound := ⟨true,true,⟨⟨(49231/5875),0,0,(-742/17625)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10239400451015731758720205 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid421 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 421) (section14Witness section14Catalog 422)) := by
  let l : CertBound := ⟨true,true,⟨⟨(5821/1025),0,0,(92/3075)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7000730190522333388913838 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid422 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 422) (section14Witness section14Catalog 423)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-10743/122617),(832214/367851),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(4840/16393),(-1/16393),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4296057703158700481449062 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid423 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 423) (section14Witness section14Catalog 424)) := by
  let l : CertBound := ⟨true,false,⟨⟨(2758456/2812381),(4872962/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4502061744287308435913714 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid424 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 424) (section14Witness section14Catalog 425)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(338631/1262218),0,0,(-67507/8835526)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (647182545066713891400102 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid425 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 425) (section14Witness section14Catalog 426)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(42027/198230),0,0,(4427/198230)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (533643400743851083205465 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid426 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 426) (section14Witness section14Catalog 427)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3466537/22624316),(2005604/5656079),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (330170578789053530307798 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid427 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 427) (section14Witness section14Catalog 428)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(16592919/31555450),0,0,(-472549/31555450)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (335617929940439045680531 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid428 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 428) (section14Witness section14Catalog 429)) := by
  let l : CertBound := ⟨true,false,⟨⟨(14528/10153),(115045/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10002460734432970689108753 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid429 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 429) (section14Witness section14Catalog 430)) := by
  let l : CertBound := ⟨true,false,⟨⟨(25229/3290),0,0,(29/1974)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7739/25486),0,0,(1/25486)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9676148782568474336821152 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid430 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 430) (section14Witness section14Catalog 431)) := by
  let l : CertBound := ⟨true,true,⟨⟨(176603/11750),0,0,(203/7050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7739/25486),0,0,(1/25486)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (19860712321111422808272533 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid431 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 431) (section14Witness section14Catalog 432)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22409/2050),0,0,(-107/6150)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13945693296742351223013056 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid432 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 432) (section14Witness section14Catalog 433)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-822279/3188042),(40094833/9564126),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(9014/29557),(-1/29557),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8672517305575186159553060 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid433 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 433) (section14Witness section14Catalog 434)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5019676/2812381),(8939102/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9065982807559337708598559 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid434 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 434) (section14Witness section14Catalog 435)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(32375/216394),0,0,(-117875/10603306)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (828104284992096546758150 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid435 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 435) (section14Witness section14Catalog 436)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(14929/108454),0,0,(-161/108454)⟩,⟨(115/422),0,0,(1/1266)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (783096438171601395623860 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid436 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 436) (section14Witness section14Catalog 437)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2453/14606),0,0,(-37/14606)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (748936461064596125583219 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid437 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 437) (section14Witness section14Catalog 438)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-710307/11933339),(1821625/11933339),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (681168154808567679284070 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid438 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 438) (section14Witness section14Catalog 439)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3115883/28206074),(5447781/28206074),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (654664819771043115853006 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid439 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 439) (section14Witness section14Catalog 440)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(923878/36425939),(4431601/36425939),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(1493/5354),(-1/16062),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (638016833180002514023851 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid440 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 440) (section14Witness section14Catalog 441)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(63455/216394),0,0,(-4715/216394)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (697254063650873589949083 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid441 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 441) (section14Witness section14Catalog 442)) := by
  let l : CertBound := ⟨true,false,⟨⟨(150525/183313),(972262/549939),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4374419820522055709506325 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid442 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 442) (section14Witness section14Catalog 443)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-979217/4427714),(27582493/13283142),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3680831851738319998101470 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid443 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 443) (section14Witness section14Catalog 444)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5449324/5431127),(24095384/16293381),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3939459093431085622303156 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid444 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 444) (section14Witness section14Catalog 445)) := by
  let l : CertBound := ⟨true,true,⟨⟨(39343/7802),0,0,(247/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6150546297493027538396730 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid445 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 445) (section14Witness section14Catalog 446)) := by
  let l : CertBound := ⟨true,false,⟨⟨(249685/61147),0,0,(15340/428029)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4872799979755361337126992 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid446 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 446) (section14Witness section14Catalog 447)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2446913/305735),0,0,(21476/305735)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10441904282190984712649841 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid447 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 447) (section14Witness section14Catalog 448)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22859/3901),0,0,(98/3901)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7234978756384865912708778 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid448 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 448) (section14Witness section14Catalog 449)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(268825/757379),0,0,(-27520/757379)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (702246101713415419413373 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid449 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 449) (section14Witness section14Catalog 450)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(8867/54227),0,0,(896/54227)⟩,⟨(115/422),0,0,(1/1266)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (631007694469245186817535 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid450 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 450) (section14Witness section14Catalog 451)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7211/36515),0,0,(704/36515)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (567224897451550940243064 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid451 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 451) (section14Witness section14Catalog 452)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-7859377/56412148),(17932221/56412148),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (392003359886922944957516 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid452 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 452) (section14Witness section14Catalog 453)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(75271/108197),0,0,(-38528/540985)⟩,⟨(233/842),0,0,(1/17682)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (450572024424658580353319 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid453 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 453) (section14Witness section14Catalog 454)) := by
  let l : CertBound := ⟨true,false,⟨⟨(273375/183313),(1783852/549939),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8825315911250635147039032 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid454 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 454) (section14Witness section14Catalog 455)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-741808/2213857),(25020023/6641571),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(8222/27073),(1/27073),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7563450905673978589185179 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid455 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 455) (section14Witness section14Catalog 456)) := by
  let l : CertBound := ⟨true,false,⟨⟨(9931204/5431127),(44192864/16293381),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8025277273392826727616739 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid456 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 456) (section14Witness section14Catalog 457)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37859/3901),0,0,(-22/3901)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (12345181028423117977960076 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid457 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 457) (section14Witness section14Catalog 458)) := by
  let l : CertBound := ⟨true,false,⟨⟨(6675455/856058),0,0,(-2935/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9619649302117572143145737 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid458 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 458) (section14Witness section14Catalog 459)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9345637/611470),0,0,(-28763/611470)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (19745728954020917892446581 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid459 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 459) (section14Witness section14Catalog 460)) := by
  let l : CertBound := ⟨true,true,⟨⟨(84343/7802),0,0,(-113/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(77/250),0,0,(-1/1750)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13815849705550405636273676 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid460 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 460) (section14Witness section14Catalog 461)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(3461375/53222218),0,0,(-28125/7603174)⟩,⟨(9683/36034),0,0,(1/36034)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (894304441567525831505432 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid461 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 461) (section14Witness section14Catalog 462)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(4543/70474),0,0,(-9/493318)⟩,⟨(89/334),0,0,(1/2338)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (871523279962129304427708 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid462 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 462) (section14Witness section14Catalog 463)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(83859/1143410),0,0,(-131/1143410)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(299/1090),0,0,(-1/1090)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (860379590464652151932261 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid463 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 463) (section14Witness section14Catalog 464)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-485017/17514937),(1272635/17514937),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (825025370268937855609750 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid464 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 464) (section14Witness section14Catalog 465)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-2144113/41398942),(11411453/124196826),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (812327149297535164520384 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid465 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 465) (section14Witness section14Catalog 466)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(5016954/464511289),(27364771/464511289),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(9257/34318),(-1/34318),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (804731842021547260920983 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid466 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 466) (section14Witness section14Catalog 467)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(969185/7603174),0,0,(-55125/7603174)⟩,⟨(9683/36034),0,0,(1/36034)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (830535771570222942821379 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid467 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 467) (section14Witness section14Catalog 468)) := by
  let l : CertBound := ⟨true,false,⟨⟨(621703/2046707),(1842270/2046707),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1619745874644154151899171 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid468 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 468) (section14Witness section14Catalog 469)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-12835643/49435846),(53625157/49435846),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1287035541360250908966487 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid469 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 469) (section14Witness section14Catalog 470)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7266892/18990023),(43323992/56970069),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1397213740649250771060640 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid470 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 470) (section14Witness section14Catalog 471)) := by
  let l : CertBound := ⟨true,true,⟨⟨(71399/25370),0,0,(-1809/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2470393447553131506418636 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid471 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 471) (section14Witness section14Catalog 472)) := by
  let l : CertBound := ⟨true,false,⟨⟨(33365/23779),0,0,(2628/23779)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1684051263611621316880981 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid472 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 472) (section14Witness section14Catalog 473)) := by
  let l : CertBound := ⟨true,true,⟨⟨(46711/16985),0,0,(18396/84925)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4187747472424285718029264 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid473 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 473) (section14Witness section14Catalog 474)) := by
  let l : CertBound := ⟨true,true,⟨⟨(41539/12685),0,0,(-1134/12685)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2990382705147121037055473 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid474 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 474) (section14Witness section14Catalog 475)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1305/9478),0,0,(-1255/199038)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (840046471534077762890526 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid475 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 475) (section14Witness section14Catalog 476)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(15/94),0,0,(-5/1974)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (769004108590544356573616 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid476 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 476) (section14Witness section14Catalog 477)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(265/1394),0,0,(-5/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (741414388148739517794024 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid477 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 477) (section14Witness section14Catalog 478)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1805/23782),(12589/71346),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (640998665516856183444040 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid478 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 478) (section14Witness section14Catalog 479)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-8035/56212),(3194/14053),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(113/179),(1/537),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (607066138960317427877186 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid479 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 479) (section14Witness section14Catalog 480)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(28051/1291466),(181029/1291466),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (584157794847644953209748 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid480 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 480) (section14Witness section14Catalog 481)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1827/6770),0,0,(-251/20310)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (670986490093383008045280 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid481 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 481) (section14Witness section14Catalog 482)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5415/6253),(12589/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(13/23),(1/69),0,0⟩,⟨(59/94),(-1/94),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5838385669179933891900608 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid482 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 482) (section14Witness section14Catalog 483)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-28051/75517),(181029/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(732/1249),(1/1249),0,0⟩,⟨(59/94),(-1/94),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4937936026880109492138619 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid483 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 483) (section14Witness section14Catalog 484)) := by
  let l : CertBound := ⟨true,false,⟨⟨(32140/30251),(51104/30251),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(13/23),(1/69),0,0⟩,⟨(59/94),(-1/94),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5265660699405834057690496 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid484 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 484) (section14Witness section14Catalog 485)) := by
  let l : CertBound := ⟨true,true,⟨⟨(53/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(15/34),0,0,(1/34)⟩,⟨(53/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7974615073976414718826703 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid485 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 485) (section14Witness section14Catalog 486)) := by
  let l : CertBound := ⟨true,false,⟨⟨(783/202),0,0,(251/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(831/1354),0,0,(-1/1354)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6380496797641577786120941 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid486 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 486) (section14Witness section14Catalog 487)) := by
  let l : CertBound := ⟨true,true,⟨⟨(38367/5050),0,0,(1757/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(831/1354),0,0,(-1/1354)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13463537042837781490679701 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid487 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 487) (section14Witness section14Catalog 488)) := by
  let l : CertBound := ⟨true,true,⟨⟨(63/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(63/94),0,0,(-1/94)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9677482132659044259825332 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid488 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 488) (section14Witness section14Catalog 489)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(445/48134),0,0,(2115/336938)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (956195786577804292499441 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid489 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 489) (section14Witness section14Catalog 490)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-37/1394),0,0,(27/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (921402706208991342234849 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid490 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 490) (section14Witness section14Catalog 491)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-536/11891),(875/11891),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (879072092976190604757682 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid491 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 491) (section14Witness section14Catalog 492)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(4361/240670),0,0,(2961/240670)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (889748238897451197556525 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid492 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 492) (section14Witness section14Catalog 493)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1330/14053),(2979/28106),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (867053484205023379448311 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid493 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 493) (section14Witness section14Catalog 494)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-4897/361537),(22359/361537),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (859218352554425943927869 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid494 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 494) (section14Witness section14Catalog 495)) := by
  let l : CertBound := ⟨true,false,⟨⟨(55/169),(121/169),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1544681518761842381046325 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid495 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 495) (section14Witness section14Catalog 496)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5313/75517),(57277/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(113/179),(1/537),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1248603375664322295394043 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid496 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 496) (section14Witness section14Catalog 497)) := by
  let l : CertBound := ⟨true,false,⟨⟨(11860/30251),(54616/90753),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1331605856621498310959325 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid497 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 497) (section14Witness section14Catalog 498)) := by
  let l : CertBound := ⟨true,false,⟨⟨(2697/1414),0,0,(-19/202)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1412302498063672495650798 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid498 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 498) (section14Witness section14Catalog 499)) := by
  let l : CertBound := ⟨true,true,⟨⟨(18879/5050),0,0,(-931/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3725876215665087121358221 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid499 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 499) (section14Witness section14Catalog 500)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2242296774984644815137212 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid500 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 500) (section14Witness section14Catalog 501)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1/235),0,0,(16/4935)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (935866468917470632388730 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid501 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 501) (section14Witness section14Catalog 502)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/1025),0,0,(28/3075)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (918811055184778433182487 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid502 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 502) (section14Witness section14Catalog 503)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1043/46079),(1720/46079),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (896093457566355801702105 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid503 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 503) (section14Witness section14Catalog 504)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(49/5875),0,0,(112/17625)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (902454755460620945339535 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid504 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 504) (section14Witness section14Catalog 505)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-5195/108914),(2926/54457),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (889963191710499122690137 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid505 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 505) (section14Witness section14Catalog 506)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-12696/2146969),(66601/2146969),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (885818400379356981879134 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid506 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 506) (section14Witness section14Catalog 507)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1064/6539),(2138/6539),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (244967698861629256516294 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid507 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 507) (section14Witness section14Catalog 508)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (227352700094487240861802 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid508 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 508) (section14Witness section14Catalog 509)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1346725127034972288766411 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid509 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 509) (section14Witness section14Catalog 510)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (715639007921699730915522 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid510 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 510) (section14Witness section14Catalog 511)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (621522497891154992752002 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid511 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 511) (section14Witness section14Catalog 512)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1155187913367833712807564 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 384).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 384).take 128 = [⟨384,[1,2,3,4,5,6,7,8,9,10,11,12],385⟩,⟨385,[1,2,3,5,6,7,9,10,11,13,14,15],386⟩,⟨386,[1,2,3,5,6,7,9,10,11,13,14,15],387⟩,⟨387,[1,2,4,5,6,8,9,10,12,13,14,16],388⟩,⟨388,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],389⟩,⟨389,[1,2,4,5,6,8,9,10,12,13,14,16],390⟩,⟨390,[1,2,3,5,6,7,13,14,15],391⟩,⟨391,[1,2,4,5,6,8,9,10,12,13,14,16],392⟩,⟨392,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],393⟩,⟨393,[1,2,3,4,5,6,7,8,13,14,15,16],394⟩,⟨394,[1,2,3,4,5,6,7,8,13,14,15,16],395⟩,⟨395,[1,2,3,4,5,6,7,8,13,14,15,16],396⟩,⟨396,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],397⟩,⟨397,[1,2,3,4,5,6,7,8,13,14,15,16],398⟩,⟨398,[1,2,3,4,5,6,7,8,13,14,15,16],399⟩,⟨399,[1,2,3,4,5,6,7,8,13,14,15,16],400⟩,⟨400,[1,4,5,6,8,9,10,12,13,16],401⟩,⟨401,[1,4,5,6,8,9,10,12,13,16],402⟩,⟨402,[1,4,5,6,8,9,10,12,13,16],403⟩,⟨403,[1,4,5,6,8,9,10,12,13,16],404⟩,⟨404,[1,4,5,6,8,9,10,12,13,16],405⟩,⟨405,[1,4,5,6,8,9,10,12,13,16],406⟩,⟨406,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],407⟩,⟨407,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],408⟩,⟨408,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],409⟩,⟨409,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],410⟩,⟨410,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],411⟩,⟨411,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],412⟩,⟨412,[1,4,5,6,8,9,10,12,13,16],413⟩,⟨413,[1,4,5,6,8,9,10,12,13,16],414⟩,⟨414,[1,4,5,6,8,9,10,12,13,16],415⟩,⟨415,[1,4,5,6,8,9,10,12,13,16],416⟩,⟨416,[1,4,5,6,8,9,10,12,13,16],417⟩,⟨417,[1,4,5,6,8,9,10,12,13,16],418⟩,⟨418,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],419⟩,⟨419,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],420⟩,⟨420,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],421⟩,⟨421,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],422⟩,⟨422,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],423⟩,⟨423,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],424⟩,⟨424,[1,4,5,6,8,9,10,12,13,16],425⟩,⟨425,[1,4,5,6,8,9,10,12,13,16],426⟩,⟨426,[1,4,5,6,8,9,10,12,13,16],427⟩,⟨427,[1,4,5,6,8,9,10,12,13,16],428⟩,⟨428,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],429⟩,⟨429,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],430⟩,⟨430,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],431⟩,⟨431,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],432⟩,⟨432,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],433⟩,⟨433,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],434⟩,⟨434,[1,4,5,6,8,9,10,12,13,16],435⟩,⟨435,[1,4,5,6,8,9,10,12,13,16],436⟩,⟨436,[1,4,5,6,8,9,10,12,13,16],437⟩,⟨437,[1,4,5,6,8,9,10,12,13,16],438⟩,⟨438,[1,4,5,6,8,9,10,12,13,16],439⟩,⟨439,[1,4,5,6,8,9,10,12,13,16],440⟩,⟨440,[1,4,5,6,8,9,10,12,13,16],441⟩,⟨441,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],442⟩,⟨442,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],443⟩,⟨443,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],444⟩,⟨444,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],445⟩,⟨445,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],446⟩,⟨446,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],447⟩,⟨447,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],448⟩,⟨448,[1,4,5,6,8,9,10,12,13,16],449⟩,⟨449,[1,4,5,6,8,9,10,12,13,16],450⟩,⟨450,[1,4,5,6,8,9,10,12,13,16],451⟩,⟨451,[1,4,5,6,8,9,10,12,13,16],452⟩,⟨452,[1,4,5,6,8,9,10,12,13,16],453⟩,⟨453,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],454⟩,⟨454,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],455⟩,⟨455,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],456⟩,⟨456,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],457⟩,⟨457,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],458⟩,⟨458,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],459⟩,⟨459,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],460⟩,⟨460,[1,4,5,6,8,9,10,12,13,16],461⟩,⟨461,[1,4,5,6,8,9,10,12,13,16],462⟩,⟨462,[1,4,5,6,8,9,10,12,13,16],463⟩,⟨463,[1,4,5,6,8,9,10,12,13,16],464⟩,⟨464,[1,4,5,6,8,9,10,12,13,16],465⟩,⟨465,[1,4,5,6,8,9,10,12,13,16],466⟩,⟨466,[1,4,5,6,8,9,10,12,13,16],467⟩,⟨467,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],468⟩,⟨468,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],469⟩,⟨469,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],470⟩,⟨470,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],471⟩,⟨471,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],472⟩,⟨472,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],473⟩,⟨473,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],474⟩,⟨474,[1,4,5,6,8,9,10,12,13,16],475⟩,⟨475,[1,4,5,6,8,9,10,12,13,16],476⟩,⟨476,[1,4,5,6,8,9,10,12,13,16],477⟩,⟨477,[1,4,5,6,8,9,10,12,13,16],478⟩,⟨478,[1,4,5,6,8,9,10,12,13,16],479⟩,⟨479,[1,4,5,6,8,9,10,12,13,16],480⟩,⟨480,[1,4,5,6,8,9,10,12,13,16],481⟩,⟨481,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],482⟩,⟨482,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],483⟩,⟨483,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],484⟩,⟨484,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],485⟩,⟨485,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],486⟩,⟨486,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],487⟩,⟨487,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],488⟩,⟨488,[1,4,5,6,8,9,10,12,13,16],489⟩,⟨489,[1,4,5,6,8,9,10,12,13,16],490⟩,⟨490,[1,4,5,6,8,9,10,12,13,16],491⟩,⟨491,[1,4,5,6,8,9,10,12,13,16],492⟩,⟨492,[1,4,5,6,8,9,10,12,13,16],493⟩,⟨493,[1,4,5,6,8,9,10,12,13,16],494⟩,⟨494,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],495⟩,⟨495,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],496⟩,⟨496,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],497⟩,⟨497,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],498⟩,⟨498,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],499⟩,⟨499,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],500⟩,⟨500,[1,4,5,6,8,9,10,12],501⟩,⟨501,[1,4,5,6,8,9,10,12],502⟩,⟨502,[1,4,5,6,8,9,10,12],503⟩,⟨503,[1,4,5,6,8,9,10,12],504⟩,⟨504,[1,4,5,6,8,9,10,12],505⟩,⟨505,[1,4,5,6,8,9,10,12],506⟩,⟨506,[1,2,3,4,5,6,7,8,9,10,11,12],507⟩,⟨507,[1,2,3,4,5,6,7,8,9,10,11,12],508⟩,⟨508,[1,2,3,4,5,6,7,8,9,10,11,12],509⟩,⟨509,[1,2,3,4,5,6,7,8,9,10,11,12],510⟩,⟨510,[1,5,6,9,10,13],511⟩,⟨511,[1,2,5,6,9,10,13,14],512⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid384
  · exact valid385
  · exact valid386
  · exact valid387
  · exact valid388
  · exact valid389
  · exact valid390
  · exact valid391
  · exact valid392
  · exact valid393
  · exact valid394
  · exact valid395
  · exact valid396
  · exact valid397
  · exact valid398
  · exact valid399
  · exact valid400
  · exact valid401
  · exact valid402
  · exact valid403
  · exact valid404
  · exact valid405
  · exact valid406
  · exact valid407
  · exact valid408
  · exact valid409
  · exact valid410
  · exact valid411
  · exact valid412
  · exact valid413
  · exact valid414
  · exact valid415
  · exact valid416
  · exact valid417
  · exact valid418
  · exact valid419
  · exact valid420
  · exact valid421
  · exact valid422
  · exact valid423
  · exact valid424
  · exact valid425
  · exact valid426
  · exact valid427
  · exact valid428
  · exact valid429
  · exact valid430
  · exact valid431
  · exact valid432
  · exact valid433
  · exact valid434
  · exact valid435
  · exact valid436
  · exact valid437
  · exact valid438
  · exact valid439
  · exact valid440
  · exact valid441
  · exact valid442
  · exact valid443
  · exact valid444
  · exact valid445
  · exact valid446
  · exact valid447
  · exact valid448
  · exact valid449
  · exact valid450
  · exact valid451
  · exact valid452
  · exact valid453
  · exact valid454
  · exact valid455
  · exact valid456
  · exact valid457
  · exact valid458
  · exact valid459
  · exact valid460
  · exact valid461
  · exact valid462
  · exact valid463
  · exact valid464
  · exact valid465
  · exact valid466
  · exact valid467
  · exact valid468
  · exact valid469
  · exact valid470
  · exact valid471
  · exact valid472
  · exact valid473
  · exact valid474
  · exact valid475
  · exact valid476
  · exact valid477
  · exact valid478
  · exact valid479
  · exact valid480
  · exact valid481
  · exact valid482
  · exact valid483
  · exact valid484
  · exact valid485
  · exact valid486
  · exact valid487
  · exact valid488
  · exact valid489
  · exact valid490
  · exact valid491
  · exact valid492
  · exact valid493
  · exact valid494
  · exact valid495
  · exact valid496
  · exact valid497
  · exact valid498
  · exact valid499
  · exact valid500
  · exact valid501
  · exact valid502
  · exact valid503
  · exact valid504
  · exact valid505
  · exact valid506
  · exact valid507
  · exact valid508
  · exact valid509
  · exact valid510
  · exact valid511
end Section14Numerical_384_512

#print axioms solution
