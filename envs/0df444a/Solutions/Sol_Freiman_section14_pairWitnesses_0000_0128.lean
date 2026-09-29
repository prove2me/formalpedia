-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_0000_0128
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T09:24:32.867273+00:00
-- url     : https://prove2.me/submissions/fca766e1-520e-41e6-8085-be1f9b0e9eb2

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_0_128
private theorem valid0 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1) (section14Witness section14Catalog 1)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1035017587139699850462958 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 2) (section14Witness section14Catalog 2)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid2 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 3) (section14Witness section14Catalog 3)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid3 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 4) (section14Witness section14Catalog 4)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1119358179718778890664383 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid4 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 5) (section14Witness section14Catalog 5)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (957031986643393338859133 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid5 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 6) (section14Witness section14Catalog 6)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (975725287196354355563425 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid6 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 7) (section14Witness section14Catalog 7)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (914335767622046090350366 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid7 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 8) (section14Witness section14Catalog 8)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (941053207850221841420584 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid8 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 9) (section14Witness section14Catalog 9)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (654478552141090691326117 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid9 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 10) (section14Witness section14Catalog 10)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/2),(5/6),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(5/7),0,0,0⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2150317022462406894173503 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid10 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 11) (section14Witness section14Catalog 11)) := by
  let l : CertBound := ⟨true,false,⟨⟨(18/157),(431/471),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1272055192506770099672432 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid11 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 12) (section14Witness section14Catalog 12)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/2),(5/6),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1641020318199398683809753 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid12 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 13) (section14Witness section14Catalog 13)) := by
  let l : CertBound := ⟨true,false,⟨⟨(65/107),(221/321),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1359235239766559112463459 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid13 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 14) (section14Witness section14Catalog 14)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2746587575245657802046412 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid14 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 15) (section14Witness section14Catalog 15)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/2),(5/6),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1468070696743200504039490 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid15 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 16) (section14Witness section14Catalog 16)) := by
  let l : CertBound := ⟨true,false,⟨⟨(65/107),(221/321),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1209430429831902960765630 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid16 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 17) (section14Witness section14Catalog 17)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2569139028648716335234259 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid17 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 18) (section14Witness section14Catalog 18)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-1/2),0,0,(59/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(5/7),0,0,0⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2749100883916481661691252 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid18 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 19) (section14Witness section14Catalog 19)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-1/2),0,0,(59/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2311971838393723790628154 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid19 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 20) (section14Witness section14Catalog 20)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-1/2),0,0,(59/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2015012412145285647323365 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid20 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 21) (section14Witness section14Catalog 21)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/50),0,0,(59/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(5/7),0,0,0⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6726970083651399761644691 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid21 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 22) (section14Witness section14Catalog 22)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/50),0,0,(59/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6373849939763117895209679 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid22 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 23) (section14Witness section14Catalog 23)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/50),0,0,(59/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5893707142728672403492580 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid23 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 24) (section14Witness section14Catalog 24)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(5/7),0,0,0⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3886883714629320107567405 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid24 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 25) (section14Witness section14Catalog 25)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3501032995912867293392551 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid25 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 26) (section14Witness section14Catalog 26)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3161052695469114890906478 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid26 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 27) (section14Witness section14Catalog 27)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (773126279802715035031067 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid27 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 28) (section14Witness section14Catalog 28)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (593916529391124304799711 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid28 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 29) (section14Witness section14Catalog 29)) := by
  let l : CertBound := ⟨true,true,⟨⟨(343/5050),0,0,(413/5050)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(343/5050),0,0,(413/5050)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid29 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 30) (section14Witness section14Catalog 30)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (983985789114278800667039 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid30 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 31) (section14Witness section14Catalog 31)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/11),(5/11),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (414493868003142664003814 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid31 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 32) (section14Witness section14Catalog 32)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/11),(5/11),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (844417443842984210982905 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid32 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 33) (section14Witness section14Catalog 33)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-15/26),(17/26),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (331741683845504792714361 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid33 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 34) (section14Witness section14Catalog 34)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-15/26),(17/26),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (755152608216741648038702 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid34 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 35) (section14Witness section14Catalog 35)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2127134317678257561016478 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid35 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 36) (section14Witness section14Catalog 36)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1949507717521094274952060 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid36 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 37) (section14Witness section14Catalog 37)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/11),(5/11),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1549079713877609059793747 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid37 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 38) (section14Witness section14Catalog 38)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1439624459877221432158513 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid38 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 39) (section14Witness section14Catalog 39)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1254271571839586710903404 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid39 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 40) (section14Witness section14Catalog 40)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-54/1177),(431/1177),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (748441716153872490829766 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid40 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 41) (section14Witness section14Catalog 41)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-11/13),(242/39),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (16780271758610070142427383 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid41 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 42) (section14Witness section14Catalog 42)) := by
  let l : CertBound := ⟨true,false,⟨⟨(625/119),0,0,(100/119)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (14174831738468970685921762 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid42 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 43) (section14Witness section14Catalog 43)) := by
  let l : CertBound := ⟨true,true,⟨⟨(175/17),0,0,(28/17)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (29189311658533159192457318 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid43 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 44) (section14Witness section14Catalog 44)) := by
  let l : CertBound := ⟨true,true,⟨⟨7,0,0,2⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (25968112590069617518751915 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid44 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 45) (section14Witness section14Catalog 45)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2057/314),(2739/314),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(101/143),(-1/429),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (14292617637973297975418598 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid45 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 46) (section14Witness section14Catalog 46)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-532/949),(5184/949),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13862007726400876671944671 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid46 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 47) (section14Witness section14Catalog 47)) := by
  let l : CertBound := ⟨true,true,⟨⟨(11/2),0,0,(3/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (20320578695800112514668698 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid47 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 48) (section14Witness section14Catalog 48)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid48 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 49) (section14Witness section14Catalog 49)) := by
  let l : CertBound := ⟨true,false,⟨⟨(15/34),0,0,(115/714)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (810570061922116262554726 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid49 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 50) (section14Witness section14Catalog 50)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2577043858650774446297332 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid50 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 51) (section14Witness section14Catalog 51)) := by
  let l : CertBound := ⟨true,false,⟨⟨(15/34),0,0,(115/714)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(15/34),0,0,(115/714)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid51 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 52) (section14Witness section14Catalog 52)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(3/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid52 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 53) (section14Witness section14Catalog 53)) := by
  let l : CertBound := ⟨true,true,⟨⟨(147/170),0,0,(161/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(147/170),0,0,(161/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid53 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 54) (section14Witness section14Catalog 54)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (265761124539338952156026 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid54 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 55) (section14Witness section14Catalog 55)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(343/5050),0,0,(413/5050)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (540502405674190057182972 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid55 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 56) (section14Witness section14Catalog 56)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (844297807780298834067427 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid56 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 57) (section14Witness section14Catalog 57)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3/143),(17/143),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (176593119778612822040338 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid57 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 58) (section14Witness section14Catalog 58)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (402897694462407474697995 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid58 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 59) (section14Witness section14Catalog 59)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (227559325417963811921876 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid59 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 60) (section14Witness section14Catalog 60)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1028751332509063959461508 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid60 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 61) (section14Witness section14Catalog 61)) := by
  let l : CertBound := ⟨true,true,⟨⟨(343/5050),0,0,(413/5050)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (650879704572219654413868 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid61 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 62) (section14Witness section14Catalog 62)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (479894321756802628097301 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid62 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 63) (section14Witness section14Catalog 63)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (275699281200580908820975 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid63 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 64) (section14Witness section14Catalog 64)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (194579445226976696055408 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid64 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 65) (section14Witness section14Catalog 65)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (332722750973677944648340 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid65 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 66) (section14Witness section14Catalog 66)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (232885558806962919649918 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid66 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 67) (section14Witness section14Catalog 67)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1042549087453516717717861 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid67 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 68) (section14Witness section14Catalog 68)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (929236609504770891803184 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid68 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 69) (section14Witness section14Catalog 69)) := by
  let l : CertBound := ⟨true,true,⟨⟨(343/5050),0,0,(413/5050)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (643318768522432914008246 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid69 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 70) (section14Witness section14Catalog 70)) := by
  let l : CertBound := ⟨true,true,⟨⟨(343/5050),0,0,(413/5050)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (566533874459110622195507 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid70 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 71) (section14Witness section14Catalog 71)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (521205750117918357192713 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid71 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 72) (section14Witness section14Catalog 72)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (406585698370191400251169 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid72 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 73) (section14Witness section14Catalog 73)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(25/119),0,0,(-4/119)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (384057512206609742434370 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid73 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 74) (section14Witness section14Catalog 74)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/5),0,0,(2/35)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (351899557150312510616571 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid74 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 75) (section14Witness section14Catalog 75)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/34),0,0,(3/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (334608539749300058790831 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid75 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 76) (section14Witness section14Catalog 76)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(3/407),(2/37),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (286865805777192294777048 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid76 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 77) (section14Witness section14Catalog 77)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(133/21164),(324/5291),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (269521753137360576720746 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid77 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 78) (section14Witness section14Catalog 78)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(17/481),(249/5291),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(101/143),(-1/429),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (257911765943582093284994 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid78 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 79) (section14Witness section14Catalog 79)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7/17),0,0,(-28/425)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (300617576270505643939912 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid79 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 80) (section14Witness section14Catalog 80)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/37),(12/37),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (800205174683201485863537 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid80 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 81) (section14Witness section14Catalog 81)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-161/5809),(2137/5809),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (640149881531054497852779 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid81 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 82) (section14Witness section14Catalog 82)) := by
  let l : CertBound := ⟨true,false,⟨⟨(30/179),(146/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (696188347520374244698864 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid82 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 83) (section14Witness section14Catalog 83)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1237257068196723550062213 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid83 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 84) (section14Witness section14Catalog 84)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (869292825777551897206370 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid84 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 85) (section14Witness section14Catalog 85)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(10755/428029),0,0,(-1340/428029)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (384130975307996129298453 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid85 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 86) (section14Witness section14Catalog 86)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-99/3901),0,0,(32/3901)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (377384820417046995207219 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid86 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 87) (section14Witness section14Catalog 87)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-59/2050),0,0,(19/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (377673683038751963858312 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid87 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 88) (section14Witness section14Catalog 88)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(76/46079),(449/46079),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (366998179152475976153772 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid88 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 89) (section14Witness section14Catalog 89)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(163/108914),(7211/653484),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (363816571244396658307304 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid89 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 90) (section14Witness section14Catalog 90)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9875/1620553),(14217/1620553),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (361944307325973228465887 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid90 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 91) (section14Witness section14Catalog 91)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(15057/305735),0,0,(-1876/305735)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (368081826347592896597176 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid91 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 92) (section14Witness section14Catalog 92)) := by
  let l : CertBound := ⟨true,false,⟨⟨(377/5533),(819/5533),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (143470658138205387333804 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid92 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 93) (section14Witness section14Catalog 93)) := by
  let l : CertBound := ⟨true,true,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (442021930522232126362646 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid93 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 94) (section14Witness section14Catalog 94)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (219059735665672540994074 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid94 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 95) (section14Witness section14Catalog 95)) := by
  let l : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (827639039961652694226101 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid95 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 96) (section14Witness section14Catalog 96)) := by
  let l : CertBound := ⟨true,true,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (545362468985016929016294 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid96 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 97) (section14Witness section14Catalog 97)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3/143),(17/143),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(3/143),(17/143),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid97 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 98) (section14Witness section14Catalog 98)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid98 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 99) (section14Witness section14Catalog 99)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid99 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 100) (section14Witness section14Catalog 100)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(85/938),0,0,(-5/938)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (302654461107786546499508 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid100 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 101) (section14Witness section14Catalog 101)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid101 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 102) (section14Witness section14Catalog 102)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/34),0,0,(3/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (249983287388731764851206 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid102 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 103) (section14Witness section14Catalog 103)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(3/407),(2/37),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (220833050913681042636321 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid103 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 104) (section14Witness section14Catalog 104)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(119/670),0,0,(-7/670)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (204114249260072747291930 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid104 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 105) (section14Witness section14Catalog 105)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid105 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 106) (section14Witness section14Catalog 106)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(25/119),0,0,(-4/119)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (334910253918462225399402 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid106 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 107) (section14Witness section14Catalog 107)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/5),0,0,(2/35)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (314245765529167141901806 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid107 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 108) (section14Witness section14Catalog 108)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/34),0,0,(3/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (300532611153257534899415 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid108 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 109) (section14Witness section14Catalog 109)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(3/407),(2/37),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (266785763164550133888777 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid109 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 110) (section14Witness section14Catalog 110)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(133/21164),(324/5291),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (244317810743284400136158 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid110 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 111) (section14Witness section14Catalog 111)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(17/481),(249/5291),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(101/143),(-1/429),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (240702251563041057632548 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid111 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 112) (section14Witness section14Catalog 112)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7/17),0,0,(-28/425)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (258911770593005346425813 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid112 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 113) (section14Witness section14Catalog 113)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(10755/428029),0,0,(-1340/428029)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (337195051057006057289764 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid113 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 114) (section14Witness section14Catalog 114)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-99/3901),0,0,(32/3901)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (332752022424913252345216 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid114 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 115) (section14Witness section14Catalog 115)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-59/2050),0,0,(19/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (333122191970023223273637 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid115 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 116) (section14Witness section14Catalog 116)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(76/46079),(449/46079),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (337724384295672563521433 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid116 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 117) (section14Witness section14Catalog 117)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(163/108914),(7211/653484),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(52/73),(1/73),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (321213202495652597609456 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid117 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 118) (section14Witness section14Catalog 118)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9875/1620553),(14217/1620553),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (333171356457918417518551 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid118 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 119) (section14Witness section14Catalog 119)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(15057/305735),0,0,(-1876/305735)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (322577218888618509043275 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid119 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 120) (section14Witness section14Catalog 120)) := by
  let l : CertBound := ⟨true,false,⟨⟨(377/5533),(819/5533),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (194203923527242761677506 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid120 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 121) (section14Witness section14Catalog 121)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(85/938),0,0,(-5/938)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (262844089642907542290360 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid121 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 122) (section14Witness section14Catalog 122)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/34),0,0,(3/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (226131005415012777086406 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid122 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 123) (section14Witness section14Catalog 123)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(50/1969),(101/1969),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (184300282926127424797098 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid123 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 124) (section14Witness section14Catalog 124)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(119/670),0,0,(-7/670)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (173092023525188387569623 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid124 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 125) (section14Witness section14Catalog 125)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(25/119),0,0,(-4/119)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (628937986709627188589171 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid125 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 126) (section14Witness section14Catalog 126)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/5),0,0,(2/35)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (599791750541205869063970 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid126 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 127) (section14Witness section14Catalog 127)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/34),0,0,(3/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (597634402653582819053492 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid127 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 128) (section14Witness section14Catalog 128)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(3/407),(2/37),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (554942815982118770094080 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 0).take 128, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 0).take 128 = [⟨1,[1,2,3,5,6,7,9,10,11,13,14,15],1⟩,⟨2,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],2⟩,⟨3,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],3⟩,⟨4,[1,2,4,5,6,8,9,10,12,13,14,16],4⟩,⟨5,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],5⟩,⟨6,[1,2,4,5,6,8,9,10,12,13,14,16],6⟩,⟨7,[1,2,3,5,6,7,13,14,15],7⟩,⟨8,[1,2,4,5,6,8,9,10,12,13,14,16],8⟩,⟨9,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],9⟩,⟨10,[1,2,3,4,5,6,7,8,13,14,15,16],10⟩,⟨11,[1,2,3,4,5,6,7,8,13,14,15,16],11⟩,⟨12,[1,2,3,4,6,7,13,14,15,16],12⟩,⟨13,[1,2,3,4,6,7,13,14,15,16],13⟩,⟨14,[1,2,3,4,6,7,11,13,14,15,16],14⟩,⟨15,[1,2,3,4,5,6,7,8,13,14,15,16],15⟩,⟨16,[1,2,3,4,5,6,7,8,13,14,15,16],16⟩,⟨17,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],17⟩,⟨18,[1,2,3,4,5,6,7,8,13,14,15,16],18⟩,⟨19,[1,2,3,4,5,6,7,8,13,14,15,16],19⟩,⟨20,[1,2,3,4,5,6,7,8,13,14,15,16],20⟩,⟨21,[1,2,3,4,5,6,7,8,13,14,15,16],21⟩,⟨22,[1,2,3,4,5,6,7,8,13,14,15,16],22⟩,⟨23,[1,2,3,4,5,6,7,8,13,14,15,16],23⟩,⟨24,[1,2,3,4,5,6,7,8,13,14,15,16],24⟩,⟨25,[1,2,3,4,5,6,7,8,13,14,15,16],25⟩,⟨26,[1,2,3,4,5,6,7,8,13,14,15,16],26⟩,⟨27,[1,2,4,5,6,8,9,10,12,13,14,16],27⟩,⟨28,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],28⟩,⟨29,[1,2,4,5,6,8,9,10,12,13,14,16],29⟩,⟨30,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],30⟩,⟨31,[1,2,4,5,6,8,9,10,12,13,14,16],31⟩,⟨32,[1,2,4,5,6,8,9,10,12,13,14,16],32⟩,⟨33,[1,2,4,5,6,8,9,10,12,13,14,16],33⟩,⟨34,[1,2,4,5,6,8,9,10,12,13,14,16],34⟩,⟨35,[1,2,4,5,6,8,9,10,12,13,14,16],35⟩,⟨36,[1,2,4,5,6,8,9,10,12,13,14,16],36⟩,⟨37,[1,2,4,5,6,8,9,10,12,13,14,16],37⟩,⟨38,[1,2,4,5,6,8,9,10,12,13,14,16],38⟩,⟨39,[1,2,4,5,6,8,9,10,12,13,14,16],39⟩,⟨40,[1,2,4,5,6,8,9,10,12,13,14,16],40⟩,⟨41,[1,2,3,4,5,6,7,8],41⟩,⟨42,[1,2,3,4,5,6,7,8,9,10,11,12],42⟩,⟨43,[1,2,3,4,5,6,7,8,9,10,11,12],43⟩,⟨44,[1,2,3,4,5,6,7,8,9,10,11,12],44⟩,⟨45,[1,2,3,4,5,6,7,8],45⟩,⟨46,[1,2,3,4,5,6,7,8,9,10,11,12],46⟩,⟨47,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],47⟩,⟨48,[1,2,3,5,6,7,13,14,15],48⟩,⟨49,[1,2,4,5,6,8,9,10,12],49⟩,⟨50,[1,2,4,5,6,8,9,10,12],50⟩,⟨51,[1,2,4,9,10],51⟩,⟨52,[1,2,4,9,12],52⟩,⟨53,[1,4,6,8,9,10],53⟩,⟨54,[1,2,3,5,6,7,13,14,15],54⟩,⟨55,[1,2,4,5,6,8,9,10,12,13,14,16],55⟩,⟨56,[1,2,3,5,6,7,9,10,11,13,14,15],56⟩,⟨57,[1,2,5,6,9,10,13,14],57⟩,⟨58,[1,2,3,5,6,7,13,14,15],58⟩,⟨59,[1,5,9,10,13],59⟩,⟨60,[1,2,3,5,6,7,13,14,15],60⟩,⟨61,[1,2,5,6,9,10,13,14],61⟩,⟨62,[1,2,3,5,6,7,9,10,13,14,15],62⟩,⟨63,[1,2,4,5,6,8,9,10,12,13,14,16],63⟩,⟨64,[1,2,4,5,6,8,9,10,12,13,14,16],64⟩,⟨65,[1,2,4,5,6,8,9,10,12,13,14,16],65⟩,⟨66,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],66⟩,⟨67,[1,2,5,6,13,14],67⟩,⟨68,[1,2,3,5,6,7,13,14,15],68⟩,⟨69,[1,2,4,5,6,8,9,10,12,13,14,16],69⟩,⟨70,[1,2,4,5,6,8,9,10,12,13,14,16],70⟩,⟨71,[1,2,4,5,6,8,9,10,12,13,14,16],71⟩,⟨72,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],72⟩,⟨73,[1,5,9,13],73⟩,⟨74,[1,5,9,13],74⟩,⟨75,[1,5,9,13],75⟩,⟨76,[1,5,9,13],76⟩,⟨77,[1,5,9,13],77⟩,⟨78,[1,5,9,13],78⟩,⟨79,[1,5,9,13],79⟩,⟨80,[1,2,5,6,9,10,12,13,14],80⟩,⟨81,[1,2,5,6,9,10,12,13,14],81⟩,⟨82,[1,2,5,6,9,10,12,13,14],82⟩,⟨83,[1,2,5,6,9,10,12,13,14],83⟩,⟨84,[1,2,4,5,6,8,9,10,12,13,14,16],84⟩,⟨85,[1,5,9],85⟩,⟨86,[1,5,9],86⟩,⟨87,[1,5,9],87⟩,⟨88,[1,5,9],88⟩,⟨89,[1,5,9],89⟩,⟨90,[1,5,9],90⟩,⟨91,[1,5,9],91⟩,⟨92,[1,2,5,6,9,10,12],92⟩,⟨93,[1,2,5,6,9,10,12],93⟩,⟨94,[1,2,5,6,9,10,12],94⟩,⟨95,[1,2,5,6,9,10,12],95⟩,⟨96,[1,2,5,6,9,10,12],96⟩,⟨97,[1,2,5,6,9,10,13,14],97⟩,⟨98,[1,2,4,5,6,8,9,10,12,13,14,16],98⟩,⟨99,[1,2,3,5,6,7,9,10,11,13,14,15],99⟩,⟨100,[1,5,9],100⟩,⟨101,[1,2,4,5,6,8,9,10,12,13,14,16],101⟩,⟨102,[1,5,9],102⟩,⟨103,[1,5,9],103⟩,⟨104,[1,5,9],104⟩,⟨105,[1,2,3,5,6,7,13,14,15],105⟩,⟨106,[1,2,3,5,6,7,9,10,11,13,14,15],106⟩,⟨107,[1,2,3,5,6,7,9,10,11,13,14,15],107⟩,⟨108,[1,2,3,5,6,7,9,10,11,13,14,15],108⟩,⟨109,[1,2,5,6,9,10,13,14],109⟩,⟨110,[1,2,3,5,6,7,9,10,11,13,14,15],110⟩,⟨111,[1,2,5,6,9,10,13,14],111⟩,⟨112,[1,2,3,5,6,7,9,10,11,13,14,15],112⟩,⟨113,[1,2,3,5,6,7,9,10,11],113⟩,⟨114,[1,2,3,5,6,7,9,10,11],114⟩,⟨115,[1,2,3,5,6,7,9,10,11],115⟩,⟨116,[1,2,5,6,9,10],116⟩,⟨117,[1,2,3,5,6,7,9,10,11],117⟩,⟨118,[1,2,5,6,9,10],118⟩,⟨119,[1,2,3,5,6,7,9,10,11],119⟩,⟨120,[1,2,5,6,9,10],120⟩,⟨121,[1,2,3,5,6,7,9,10,11],121⟩,⟨122,[1,2,3,5,6,7,9,10,11],122⟩,⟨123,[1,2,5,6,9,10],123⟩,⟨124,[1,2,3,5,6,7,9,10,11],124⟩,⟨125,[1,2,3,5,6,7,13,14,15],125⟩,⟨126,[1,2,3,5,6,7,13,14,15],126⟩,⟨127,[1,2,3,5,6,7,13,14,15],127⟩,⟨128,[1,2,5,6,13,14],128⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid0
  · exact valid1
  · exact valid2
  · exact valid3
  · exact valid4
  · exact valid5
  · exact valid6
  · exact valid7
  · exact valid8
  · exact valid9
  · exact valid10
  · exact valid11
  · exact valid12
  · exact valid13
  · exact valid14
  · exact valid15
  · exact valid16
  · exact valid17
  · exact valid18
  · exact valid19
  · exact valid20
  · exact valid21
  · exact valid22
  · exact valid23
  · exact valid24
  · exact valid25
  · exact valid26
  · exact valid27
  · exact valid28
  · exact valid29
  · exact valid30
  · exact valid31
  · exact valid32
  · exact valid33
  · exact valid34
  · exact valid35
  · exact valid36
  · exact valid37
  · exact valid38
  · exact valid39
  · exact valid40
  · exact valid41
  · exact valid42
  · exact valid43
  · exact valid44
  · exact valid45
  · exact valid46
  · exact valid47
  · exact valid48
  · exact valid49
  · exact valid50
  · exact valid51
  · exact valid52
  · exact valid53
  · exact valid54
  · exact valid55
  · exact valid56
  · exact valid57
  · exact valid58
  · exact valid59
  · exact valid60
  · exact valid61
  · exact valid62
  · exact valid63
  · exact valid64
  · exact valid65
  · exact valid66
  · exact valid67
  · exact valid68
  · exact valid69
  · exact valid70
  · exact valid71
  · exact valid72
  · exact valid73
  · exact valid74
  · exact valid75
  · exact valid76
  · exact valid77
  · exact valid78
  · exact valid79
  · exact valid80
  · exact valid81
  · exact valid82
  · exact valid83
  · exact valid84
  · exact valid85
  · exact valid86
  · exact valid87
  · exact valid88
  · exact valid89
  · exact valid90
  · exact valid91
  · exact valid92
  · exact valid93
  · exact valid94
  · exact valid95
  · exact valid96
  · exact valid97
  · exact valid98
  · exact valid99
  · exact valid100
  · exact valid101
  · exact valid102
  · exact valid103
  · exact valid104
  · exact valid105
  · exact valid106
  · exact valid107
  · exact valid108
  · exact valid109
  · exact valid110
  · exact valid111
  · exact valid112
  · exact valid113
  · exact valid114
  · exact valid115
  · exact valid116
  · exact valid117
  · exact valid118
  · exact valid119
  · exact valid120
  · exact valid121
  · exact valid122
  · exact valid123
  · exact valid124
  · exact valid125
  · exact valid126
  · exact valid127
end Section14Numerical_0_128

#print axioms solution
