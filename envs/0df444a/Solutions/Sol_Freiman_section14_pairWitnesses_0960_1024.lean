-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_0960_1024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:41:11.462556+00:00
-- url     : https://prove2.me/submissions/2e620c23-1bc0-410b-bda2-c21cfe9e4b27

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_960_1024
private theorem valid960 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 957) (section14Witness section14Catalog 961)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (407520954998690771453108 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid961 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 958) (section14Witness section14Catalog 962)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1042425307287184674719092 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid962 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 959) (section14Witness section14Catalog 963)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1755/1414),0,0,(155/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7101/5980),(-2999/5980),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2114061561547314457567776 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid963 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 960) (section14Witness section14Catalog 964)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2457/1010),0,0,(217/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4640402457258355271576156 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid964 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 961) (section14Witness section14Catalog 965)) := by
  let l : CertBound := ⟨true,true,⟨⟨(21/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(712411/670462),(-272773/670462),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3298434319035860859835073 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid965 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 962) (section14Witness section14Catalog 966)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-17977/18722),(13591/18722),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (345442591827276989663627 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid966 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 963) (section14Witness section14Catalog 967)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(170617/98087),(-79896/98087),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (291996867672428158168919 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid967 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 964) (section14Witness section14Catalog 968)) := by
  let l : CertBound := ⟨true,true,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (280890840359820156019324 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid968 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 965) (section14Witness section14Catalog 969)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5415/6253),(12589/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7106190433256962444126296 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid969 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 966) (section14Witness section14Catalog 970)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3189/75517),(165244/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6102151665422698979995169 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid970 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 967) (section14Witness section14Catalog 971)) := by
  let l : CertBound := ⟨true,false,⟨⟨(32140/30251),(51104/30251),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6403728111482530869017437 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid971 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 968) (section14Witness section14Catalog 972)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7051/1414),0,0,(-229/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6906532633427874384998927 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid972 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 969) (section14Witness section14Catalog 973)) := by
  let l : CertBound := ⟨true,true,⟨⟨(49357/5050),0,0,(-1603/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (14763477092090080504734381 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid973 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 970) (section14Witness section14Catalog 974)) := by
  let l : CertBound := ⟨true,true,⟨⟨(53/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9886698067519786095157598 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid974 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 971) (section14Witness section14Catalog 975)) := by
  let l : CertBound := ⟨true,false,⟨⟨(8018/10153),(62695/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6787554620032467432098585 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid975 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 972) (section14Witness section14Catalog 976)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7033/1645),0,0,(-106/4935)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6461572996417749285867406 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid976 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 973) (section14Witness section14Catalog 977)) := by
  let l : CertBound := ⟨true,true,⟨⟨(49231/5875),0,0,(-742/17625)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13788853063053729911687976 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid977 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 974) (section14Witness section14Catalog 978)) := by
  let l : CertBound := ⟨true,true,⟨⟨(5821/1025),0,0,(92/3075)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9451756475678645540175053 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid978 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 975) (section14Witness section14Catalog 979)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-10743/122617),(832214/367851),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(4840/16393),(-1/16393),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5830118752643014818784493 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid979 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 976) (section14Witness section14Catalog 980)) := by
  let l : CertBound := ⟨true,false,⟨⟨(2758456/2812381),(4872962/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6106003657692697507462775 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid980 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 977) (section14Witness section14Catalog 981)) := by
  let l : CertBound := ⟨true,false,⟨⟨(14528/10153),(115045/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13471158479558504128611811 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid981 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 978) (section14Witness section14Catalog 982)) := by
  let l : CertBound := ⟨true,false,⟨⟨(25229/3290),0,0,(29/1974)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7739/25486),0,0,(1/25486)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13034642687223360677242856 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid982 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 979) (section14Witness section14Catalog 983)) := by
  let l : CertBound := ⟨true,true,⟨⟨(176603/11750),0,0,(203/7050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7739/25486),0,0,(1/25486)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (26672069657032728238783857 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid983 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 980) (section14Witness section14Catalog 984)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22409/2050),0,0,(-107/6150)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (18751264187586521038496524 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid984 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 981) (section14Witness section14Catalog 985)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-822279/3188042),(40094833/9564126),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(9014/29557),(-1/29557),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11690325524234759144779141 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid985 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 982) (section14Witness section14Catalog 986)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5019676/2812381),(8939102/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (12217226780883245547547201 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid986 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 983) (section14Witness section14Catalog 987)) := by
  let l : CertBound := ⟨true,false,⟨⟨(340915/366626),(2173417/1099878),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6734557026872644683254314 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid987 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 984) (section14Witness section14Catalog 988)) := by
  let l : CertBound := ⟨true,false,⟨⟨(333569/2213857),(4708518/2213857),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1721/6218),(1/18654),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5794433610727452771475314 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid988 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 985) (section14Witness section14Catalog 989)) := by
  let l : CertBound := ⟨true,false,⟨⟨(6143682/5431127),(26944342/16293381),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6086693428471513428800896 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid989 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 986) (section14Witness section14Catalog 990)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5252175/856058),0,0,(-340975/856058)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6658261094452439213576063 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid990 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 987) (section14Witness section14Catalog 991)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1470609/122294),0,0,(-95473/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (14167416654499747574233867 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid991 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 988) (section14Witness section14Catalog 992)) := by
  let l : CertBound := ⟨true,true,⟨⟨(41457/7802),0,0,(667/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9195196951151662989273158 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid992 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 989) (section14Witness section14Catalog 993)) := by
  let l : CertBound := ⟨true,false,⟨⟨(2890089/4093414),(8630185/4093414),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6718547935529488575831756 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid993 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 990) (section14Witness section14Catalog 994)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-5694477/24717923),(57954242/24717923),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(10229/38062),(1/38062),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5765947615330326532226085 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid994 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 991) (section14Witness section14Catalog 995)) := by
  let l : CertBound := ⟨true,false,⟨⟨(16935298/18990023),(33820466/18990023),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6029610292481346850651045 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid995 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 992) (section14Witness section14Catalog 996)) := by
  let l : CertBound := ⟨true,false,⟨⟨(181841/47558),0,0,(21097/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(8711/32290),0,0,(-1/32290)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6278375583709040772753048 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid996 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 993) (section14Witness section14Catalog 997)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1272887/169850),0,0,(21097/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(8711/32290),0,0,(-1/32290)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13415958318588849770604552 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid997 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 994) (section14Witness section14Catalog 998)) := by
  let l : CertBound := ⟨true,true,⟨⟨(171841/25370),0,0,(-4981/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(299/1090),0,0,(-1/1090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9460781207338384669447777 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid998 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 995) (section14Witness section14Catalog 999)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1415473/4093414),(4117105/4093414),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2632182697813702783048819 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid999 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 996) (section14Witness section14Catalog 1000)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-1726029/24717923),(27246026/24717923),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(1721/6218),(1/18654),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2181210666591521059441034 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1000 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 997) (section14Witness section14Catalog 1001)) := by
  let l : CertBound := ⟨true,false,⟨⟨(8220306/18990023),(48427846/56970069),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2300726496747562817418499 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1001 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 998) (section14Witness section14Catalog 1002)) := by
  let l : CertBound := ⟨true,false,⟨⟨(89385/47558),0,0,(4225/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2359938316342519405477774 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1002 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 999) (section14Witness section14Catalog 1003)) := by
  let l : CertBound := ⟨true,true,⟨⟨(125139/33970),0,0,(169/6794)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5735821274550467890745016 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1003 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1000) (section14Witness section14Catalog 1004)) := by
  let l : CertBound := ⟨true,true,⟨⟨(14949/5074),0,0,(-233/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3810561981279356578423046 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1004 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1001) (section14Witness section14Catalog 1005)) := by
  let l : CertBound := ⟨true,false,⟨⟨(150525/183313),(972262/549939),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5937163303381449540134559 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1005 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1002) (section14Witness section14Catalog 1006)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-979217/4427714),(27582493/13283142),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5008428828346711909271410 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1006 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1003) (section14Witness section14Catalog 1007)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5449324/5431127),(24095384/16293381),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5354704699546952341868039 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1007 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1004) (section14Witness section14Catalog 1008)) := by
  let l : CertBound := ⟨true,true,⟨⟨(39343/7802),0,0,(247/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8315445846762852806141919 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1008 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1005) (section14Witness section14Catalog 1009)) := by
  let l : CertBound := ⟨true,false,⟨⟨(249685/61147),0,0,(15340/428029)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6604133149950825397834148 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1009 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1006) (section14Witness section14Catalog 1010)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2446913/305735),0,0,(21476/305735)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (14061325883276584495379714 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1010 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1007) (section14Witness section14Catalog 1011)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22859/3901),0,0,(98/3901)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9767532468429117160011842 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1011 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1008) (section14Witness section14Catalog 1012)) := by
  let l : CertBound := ⟨true,false,⟨⟨(273375/183313),(1783852/549939),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11897042699077660433385791 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1012 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1009) (section14Witness section14Catalog 1013)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-741808/2213857),(25020023/6641571),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(8222/27073),(1/27073),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10207368733749178013665426 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1013 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1010) (section14Witness section14Catalog 1014)) := by
  let l : CertBound := ⟨true,false,⟨⟨(9931204/5431127),(44192864/16293381),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10825734148209928041259054 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1014 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1011) (section14Witness section14Catalog 1015)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37859/3901),0,0,(-22/3901)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (16610242028061924526193398 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1015 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1012) (section14Witness section14Catalog 1016)) := by
  let l : CertBound := ⟨true,false,⟨⟨(6675455/856058),0,0,(-2935/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (12960302535650882664368156 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1016 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1013) (section14Witness section14Catalog 1017)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9345637/611470),0,0,(-28763/611470)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (26519417879248696737786369 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1017 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1014) (section14Witness section14Catalog 1018)) := by
  let l : CertBound := ⟨true,true,⟨⟨(84343/7802),0,0,(-113/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(77/250),0,0,(-1/1750)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (18579510186212063855414253 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1018 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1015) (section14Witness section14Catalog 1019)) := by
  let l : CertBound := ⟨true,false,⟨⟨(621703/2046707),(1842270/2046707),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2249677315019252412294868 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1019 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1016) (section14Witness section14Catalog 1020)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-12835643/49435846),(53625157/49435846),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1804168496198598790514749 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1020 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1017) (section14Witness section14Catalog 1021)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7266892/18990023),(43323992/56970069),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1951683266221144270441625 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1021 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1018) (section14Witness section14Catalog 1022)) := by
  let l : CertBound := ⟨true,true,⟨⟨(71399/25370),0,0,(-1809/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3388718168059212912068726 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1022 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1019) (section14Witness section14Catalog 1023)) := by
  let l : CertBound := ⟨true,false,⟨⟨(33365/23779),0,0,(2628/23779)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2335604074769732958228629 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1023 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1020) (section14Witness section14Catalog 1024)) := by
  let l : CertBound := ⟨true,true,⟨⟨(46711/16985),0,0,(18396/84925)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5688126161067806454136692 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 960).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 960).take 64 = [⟨957,[3,7,11,15],961⟩,⟨958,[3,7,11,15],962⟩,⟨959,[3,7,11,15],963⟩,⟨960,[3,7,11,15],964⟩,⟨961,[3,7,11,15],965⟩,⟨962,[3,7,11],966⟩,⟨963,[3,7,11],967⟩,⟨964,[3,7],968⟩,⟨965,[3,5,6,7],969⟩,⟨966,[3,5,6,7],970⟩,⟨967,[3,5,6,7],971⟩,⟨968,[3,5,6,7],972⟩,⟨969,[3,5,6,7],973⟩,⟨970,[3,5,6,7],974⟩,⟨971,[3,5,6,7],975⟩,⟨972,[3,5,6,7],976⟩,⟨973,[3,5,6,7],977⟩,⟨974,[3,5,6,7],978⟩,⟨975,[3,5,6,7],979⟩,⟨976,[3,5,6,7],980⟩,⟨977,[3,5,6,7],981⟩,⟨978,[3,5,6,7],982⟩,⟨979,[3,5,6,7],983⟩,⟨980,[3,5,6,7],984⟩,⟨981,[3,5,6,7],985⟩,⟨982,[3,5,6,7],986⟩,⟨983,[3,5,6,7],987⟩,⟨984,[3,5,6,7],988⟩,⟨985,[3,5,6,7],989⟩,⟨986,[3,5,6,7],990⟩,⟨987,[3,5,6,7],991⟩,⟨988,[3,5,6,7],992⟩,⟨989,[3,5,6,7],993⟩,⟨990,[3,5,6,7],994⟩,⟨991,[3,5,6,7],995⟩,⟨992,[3,5,6,7],996⟩,⟨993,[3,5,6,7],997⟩,⟨994,[3,5,6,7],998⟩,⟨995,[3,5,6,7],999⟩,⟨996,[3,5,6,7],1000⟩,⟨997,[3,5,6,7],1001⟩,⟨998,[3,5,6,7],1002⟩,⟨999,[3,5,6,7],1003⟩,⟨1000,[3,5,6,7],1004⟩,⟨1001,[3,5,6,7],1005⟩,⟨1002,[3,5,6,7],1006⟩,⟨1003,[3,5,6,7],1007⟩,⟨1004,[3,5,6,7],1008⟩,⟨1005,[3,5,6,7],1009⟩,⟨1006,[3,5,6,7],1010⟩,⟨1007,[3,5,6,7],1011⟩,⟨1008,[3,5,6,7],1012⟩,⟨1009,[3,5,6,7],1013⟩,⟨1010,[3,5,6,7],1014⟩,⟨1011,[3,5,6,7],1015⟩,⟨1012,[3,5,6,7],1016⟩,⟨1013,[3,5,6,7],1017⟩,⟨1014,[3,5,6,7],1018⟩,⟨1015,[3,5,6,7],1019⟩,⟨1016,[3,5,6,7],1020⟩,⟨1017,[3,5,6,7],1021⟩,⟨1018,[3,5,6,7],1022⟩,⟨1019,[3,5,6,7],1023⟩,⟨1020,[3,5,6,7],1024⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid960
  · exact valid961
  · exact valid962
  · exact valid963
  · exact valid964
  · exact valid965
  · exact valid966
  · exact valid967
  · exact valid968
  · exact valid969
  · exact valid970
  · exact valid971
  · exact valid972
  · exact valid973
  · exact valid974
  · exact valid975
  · exact valid976
  · exact valid977
  · exact valid978
  · exact valid979
  · exact valid980
  · exact valid981
  · exact valid982
  · exact valid983
  · exact valid984
  · exact valid985
  · exact valid986
  · exact valid987
  · exact valid988
  · exact valid989
  · exact valid990
  · exact valid991
  · exact valid992
  · exact valid993
  · exact valid994
  · exact valid995
  · exact valid996
  · exact valid997
  · exact valid998
  · exact valid999
  · exact valid1000
  · exact valid1001
  · exact valid1002
  · exact valid1003
  · exact valid1004
  · exact valid1005
  · exact valid1006
  · exact valid1007
  · exact valid1008
  · exact valid1009
  · exact valid1010
  · exact valid1011
  · exact valid1012
  · exact valid1013
  · exact valid1014
  · exact valid1015
  · exact valid1016
  · exact valid1017
  · exact valid1018
  · exact valid1019
  · exact valid1020
  · exact valid1021
  · exact valid1022
  · exact valid1023
end Section14Numerical_960_1024

#print axioms solution
