-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_1216_1280
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:39:44.322138+00:00
-- url     : https://prove2.me/submissions/943f8899-6b7d-4d95-b069-773b48ceb12b

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_1216_1280
private theorem valid1216 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1213) (section14Witness section14Catalog 1217)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22477/11750),0,0,(-343/11750)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(12655/20279),0,0,(-810/20279)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1844253627684121175374507 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1217 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1214) (section14Witness section14Catalog 1218)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2317/2050),0,0,(53/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(12655/20279),0,0,(-810/20279)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1110102088469450772454840 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1218 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1215) (section14Witness section14Catalog 1219)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-13/122617),(180544/367851),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(581/1025),0,0,(4/1025)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (362366824288677572736768 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1219 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1216) (section14Witness section14Catalog 1220)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3211/3290),0,0,(-7/470)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(581/1025),0,0,(4/1025)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (440704630203092084020329 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1220 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1217) (section14Witness section14Catalog 1221)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22477/11750),0,0,(-343/11750)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(581/1025),0,0,(4/1025)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1639941326809842394241349 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1221 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1218) (section14Witness section14Catalog 1222)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2317/2050),0,0,(53/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(581/1025),0,0,(4/1025)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (906666613448308361326716 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1222 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1219) (section14Witness section14Catalog 1223)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3631/20306),(9205/20306),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (277711305629660387454200 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1223 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1220) (section14Witness section14Catalog 1224)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3211/3290),0,0,(-7/470)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (186214308678298830091504 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1224 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1221) (section14Witness section14Catalog 1225)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22477/11750),0,0,(-343/11750)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1534902280448595024008289 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1225 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1222) (section14Witness section14Catalog 1226)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2317/2050),0,0,(53/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (725982980918968264606922 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1226 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1223) (section14Witness section14Catalog 1227)) := by
  let l : CertBound := ⟨true,true,⟨⟨(618801/2812381),(1073927/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (145686045516963494110474 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1227 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1224) (section14Witness section14Catalog 1228)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(70396/195767),(-42807/391534),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (687650306350799137671104 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1228 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1225) (section14Witness section14Catalog 1229)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(55067123/157719419),(-48748585/473158257),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (686864416745536327742426 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1229 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1226) (section14Witness section14Catalog 1230)) := by
  let l : CertBound := ⟨true,true,⟨⟨(17717/14485),0,0,(-1134/14485)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(70396/195767),(-42807/391534),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (958018567658508051975661 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1230 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1227) (section14Witness section14Catalog 1231)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(75657963/216909836),(-22149867/216909836),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (684895082149134843053205 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1231 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1228) (section14Witness section14Catalog 1232)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2049/6887),(2368/6887),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (769462139705751653007534 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1232 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1229) (section14Witness section14Catalog 1233)) := by
  let l : CertBound := ⟨true,true,⟨⟨(27753/99116),(34313/99116),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (748346854458073815771217 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1233 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1230) (section14Witness section14Catalog 1234)) := by
  let l : CertBound := ⟨true,true,⟨⟨(76565/242209),(79485/242209),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (756331270051137515951900 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1234 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1231) (section14Witness section14Catalog 1235)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2049/6887),(2368/6887),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(71/235),0,0,(34/1645)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (716421042664802093749337 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1235 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1232) (section14Witness section14Catalog 1236)) := by
  let l : CertBound := ⟨true,true,⟨⟨(27753/99116),(34313/99116),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(581/1025),0,0,(4/1025)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (430867597488995127714853 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1236 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1233) (section14Witness section14Catalog 1237)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2049/6887),(2368/6887),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(5/7),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (268570787213279018349310 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1237 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1234) (section14Witness section14Catalog 1238)) := by
  let l : CertBound := ⟨true,true,⟨⟨(76565/242209),(79485/242209),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(5/7),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (255040624532527501981058 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1238 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1235) (section14Witness section14Catalog 1239)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7565/68302),(13814/34151),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(71/235),0,0,(34/1645)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (603153155555720754085362 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1239 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1236) (section14Witness section14Catalog 1240)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9201/154141),(65906/154141),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(581/1025),0,0,(4/1025)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (320791968204729424152640 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1240 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1237) (section14Witness section14Catalog 1241)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7565/68302),(13814/34151),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (75053746688468030926610 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1241 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1238) (section14Witness section14Catalog 1242)) := by
  let l : CertBound := ⟨true,true,⟨⟨(365445/2402114),(2710495/7206342),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (61378856783474502564579 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1242 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1239) (section14Witness section14Catalog 1243)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(71/235),0,0,(34/1645)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1507448997267179629899608 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1243 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1240) (section14Witness section14Catalog 1244)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(581/1025),0,0,(4/1025)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1234282100320880753569555 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1244 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1241) (section14Witness section14Catalog 1245)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1071009817535806385754828 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1245 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1242) (section14Witness section14Catalog 1246)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(71/235),0,0,(34/1645)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (943324590821021310120907 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1246 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1243) (section14Witness section14Catalog 1247)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(581/1025),0,0,(4/1025)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (673978658964448360107311 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1247 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1244) (section14Witness section14Catalog 1248)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (460637155552550665819643 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1248 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1245) (section14Witness section14Catalog 1249)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/17),0,0,(4/51)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (634399711298735404144727 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1249 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1246) (section14Witness section14Catalog 1250)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-17977/18722),(13591/18722),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (475787380939473794418472 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1250 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1247) (section14Witness section14Catalog 1251)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(170617/98087),(-79896/98087),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (423535823190251852888008 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1251 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1248) (section14Witness section14Catalog 1252)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-51305/121693),(161332/365079),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (399366579768939725680565 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1252 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1249) (section14Witness section14Catalog 1253)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3722372898157243967854 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1253 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1250) (section14Witness section14Catalog 1254)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/34),0,0,(3/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (661278143099375165300724 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1254 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1251) (section14Witness section14Catalog 1255)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-144/253),(101/253),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (526897453111311939805313 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1255 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1252) (section14Witness section14Catalog 1256)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(3775/5302),(-1753/5302),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (492163867316606530409593 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1256 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1253) (section14Witness section14Catalog 1257)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-877/3289),(775/3289),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(101/143),(-1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (479301945958703781508934 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1257 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1254) (section14Witness section14Catalog 1258)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-59/2050),0,0,(19/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (677371179395044064589461 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1258 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1255) (section14Witness section14Catalog 1259)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-9641/96347),(6814/96347),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (650351365194816710675677 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1259 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1256) (section14Witness section14Catalog 1260)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(254775/2019098),(-351901/6057294),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (643979806393928615205244 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1260 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1257) (section14Witness section14Catalog 1261)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-181699/3388429),(155329/3388429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (642042329496938870102017 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1261 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1258) (section14Witness section14Catalog 1262)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1262 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1259) (section14Witness section14Catalog 1263)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-144/253),(101/253),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (410596549309135584306196 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1263 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1260) (section14Witness section14Catalog 1264)) := by
  let l : CertBound := ⟨true,false,⟨⟨(4805/3133),(-2208/3133),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (126667222447105714780700 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1264 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1261) (section14Witness section14Catalog 1265)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-9641/96347),(6814/96347),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/2),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1020457422339002793691576 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1265 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1262) (section14Witness section14Catalog 1266)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(254775/2019098),(-351901/6057294),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/2),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1011468566841384525080949 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1266 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1263) (section14Witness section14Catalog 1267)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-181699/3388429),(155329/3388429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/2),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1009092073865568074992493 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1267 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1264) (section14Witness section14Catalog 1268)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-22716/31993),(18917/31993),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-22716/31993),(18917/31993),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1268 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1265) (section14Witness section14Catalog 1269)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-144/253),(101/253),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/2),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (705595979061140058445283 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1269 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1266) (section14Witness section14Catalog 1270)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (0 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1270 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1267) (section14Witness section14Catalog 1271)) := by
  let l : CertBound := ⟨true,false,⟨⟨(161/500),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,-1,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-144/253),(101/253),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (544448840749415015362988 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1271 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1268) (section14Witness section14Catalog 1272)) := by
  let l : CertBound := ⟨true,false,⟨⟨(161/500),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,-1,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(3775/5302),(-1753/5302),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (512921093543240690886954 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1272 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1269) (section14Witness section14Catalog 1273)) := by
  let l : CertBound := ⟨true,false,⟨⟨(161/500),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,-1,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-877/3289),(775/3289),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(101/143),(-1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (501362743100861245258387 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1273 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1270) (section14Witness section14Catalog 1274)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2497/2050),0,0,(273/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(975571/385388),(-3072059/2890410),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1734932368758476254893204 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1274 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1271) (section14Witness section14Catalog 1275)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1875/6794),0,0,(1675/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1451187900884783289069918 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1275 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1272) (section14Witness section14Catalog 1276)) := by
  let l : CertBound := ⟨true,false,⟨⟨(18/157),(431/471),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2247487461479706972073251 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1276 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1273) (section14Witness section14Catalog 1277)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/2),(5/6),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2836562552771874215865233 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1277 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1274) (section14Witness section14Catalog 1278)) := by
  let l : CertBound := ⟨true,false,⟨⟨(65/107),(221/321),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2504147635782289331355011 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1278 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1275) (section14Witness section14Catalog 1279)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3354798408146708966906451 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1279 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1276) (section14Witness section14Catalog 1280)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-1/2),0,0,(59/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3819074180230369187994544 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 1216).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 1216).take 64 = [⟨1213,[3,5,7,8,9,11,12,15],1217⟩,⟨1214,[3,5,7,8,9,11,12,15],1218⟩,⟨1215,[3,5,7,8,9,11,12,15],1219⟩,⟨1216,[3,5,7,8,9,11,12,15],1220⟩,⟨1217,[3,5,7,8,9,11,12,15],1221⟩,⟨1218,[3,5,7,8,9,11,12,15],1222⟩,⟨1219,[3,7,11,15],1223⟩,⟨1220,[3,7,11,15],1224⟩,⟨1221,[3,7,11,15],1225⟩,⟨1222,[3,7,11,15],1226⟩,⟨1223,[3,7,11,15],1227⟩,⟨1224,[3,7,11,15],1228⟩,⟨1225,[3,7,11,15],1229⟩,⟨1226,[3,7,11,15],1230⟩,⟨1227,[3,7,11,15],1231⟩,⟨1228,[3,5,7,8,9,11,12,15],1232⟩,⟨1229,[3,5,7,8,9,11,12,15],1233⟩,⟨1230,[3,5,7,8,9,11,12,15],1234⟩,⟨1231,[3,5,7,8,9,11,12,15],1235⟩,⟨1232,[3,5,7,8,9,11,12,15],1236⟩,⟨1233,[3,7,11,15],1237⟩,⟨1234,[3,7,11,15],1238⟩,⟨1235,[3,5,7,8,9,11,12,15],1239⟩,⟨1236,[3,5,7,8,9,11,12,15],1240⟩,⟨1237,[3,7,11,15],1241⟩,⟨1238,[3,7,11,15],1242⟩,⟨1239,[3,5,7,8,9,11,12,15],1243⟩,⟨1240,[3,5,7,8,9,11,12,15],1244⟩,⟨1241,[3,7,11,15],1245⟩,⟨1242,[3,5,7,8,9,11,12,15],1246⟩,⟨1243,[3,5,7,8,9,11,12,15],1247⟩,⟨1244,[3,7,11,15],1248⟩,⟨1245,[3,5,7,8,9,11,12],1249⟩,⟨1246,[3,7,11],1250⟩,⟨1247,[3,7,11],1251⟩,⟨1248,[3,7,11],1252⟩,⟨1249,[4,8,16],1253⟩,⟨1250,[4,8,12,16],1254⟩,⟨1251,[4,8,12,16],1255⟩,⟨1252,[4,8,12,16],1256⟩,⟨1253,[4,8,12,16],1257⟩,⟨1254,[4,8,12],1258⟩,⟨1255,[4,8,12],1259⟩,⟨1256,[4,8,12],1260⟩,⟨1257,[4,8,12],1261⟩,⟨1258,[4,8,12,16],1262⟩,⟨1259,[4,8,12],1263⟩,⟨1260,[4,8,12,16],1264⟩,⟨1261,[4],1265⟩,⟨1262,[4],1266⟩,⟨1263,[4],1267⟩,⟨1264,[4,8,12,16],1268⟩,⟨1265,[4],1269⟩,⟨1266,[4,8,12,16],1270⟩,⟨1267,[4,8,12],1271⟩,⟨1268,[4,8,12],1272⟩,⟨1269,[4,8,12],1273⟩,⟨1270,[4,5,8,9,12,16],1274⟩,⟨1271,[4,8,9,12,16],1275⟩,⟨1272,[4,8,16],1276⟩,⟨1273,[4,8,16],1277⟩,⟨1274,[4,8,16],1278⟩,⟨1275,[4,8,9,12,16],1279⟩,⟨1276,[4,8,16],1280⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid1216
  · exact valid1217
  · exact valid1218
  · exact valid1219
  · exact valid1220
  · exact valid1221
  · exact valid1222
  · exact valid1223
  · exact valid1224
  · exact valid1225
  · exact valid1226
  · exact valid1227
  · exact valid1228
  · exact valid1229
  · exact valid1230
  · exact valid1231
  · exact valid1232
  · exact valid1233
  · exact valid1234
  · exact valid1235
  · exact valid1236
  · exact valid1237
  · exact valid1238
  · exact valid1239
  · exact valid1240
  · exact valid1241
  · exact valid1242
  · exact valid1243
  · exact valid1244
  · exact valid1245
  · exact valid1246
  · exact valid1247
  · exact valid1248
  · exact valid1249
  · exact valid1250
  · exact valid1251
  · exact valid1252
  · exact valid1253
  · exact valid1254
  · exact valid1255
  · exact valid1256
  · exact valid1257
  · exact valid1258
  · exact valid1259
  · exact valid1260
  · exact valid1261
  · exact valid1262
  · exact valid1263
  · exact valid1264
  · exact valid1265
  · exact valid1266
  · exact valid1267
  · exact valid1268
  · exact valid1269
  · exact valid1270
  · exact valid1271
  · exact valid1272
  · exact valid1273
  · exact valid1274
  · exact valid1275
  · exact valid1276
  · exact valid1277
  · exact valid1278
  · exact valid1279
end Section14Numerical_1216_1280

#print axioms solution
