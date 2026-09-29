-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_1280_1344
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:43:58.785808+00:00
-- url     : https://prove2.me/submissions/cf2c004e-3025-45b7-9ba0-5312129e699b

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_1280_1344
private theorem valid1280 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1277) (section14Witness section14Catalog 1281)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/50),0,0,(59/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9077467501621432129305729 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1281 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1278) (section14Witness section14Catalog 1282)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5469650928598802463409343 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1282 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1279) (section14Witness section14Catalog 1283)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5415/6253),(12589/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6082331433033603259644501 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1283 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1280) (section14Witness section14Catalog 1284)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3189/75517),(165244/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5214381590467731002809036 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1284 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1281) (section14Witness section14Catalog 1285)) := by
  let l : CertBound := ⟨true,false,⟨⟨(32140/30251),(51104/30251),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5477698833110260992246450 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1285 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1282) (section14Witness section14Catalog 1286)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7051/1414),0,0,(-229/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5942012712974344159090733 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1286 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1283) (section14Witness section14Catalog 1287)) := by
  let l : CertBound := ⟨true,true,⟨⟨(49357/5050),0,0,(-1603/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (12735421466849278344024665 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1287 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1284) (section14Witness section14Catalog 1288)) := by
  let l : CertBound := ⟨true,true,⟨⟨(53/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8537508865616707729068273 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1288 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1285) (section14Witness section14Catalog 1289)) := by
  let l : CertBound := ⟨true,false,⟨⟨(8018/10153),(62695/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5515541687575220772659088 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1289 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1286) (section14Witness section14Catalog 1290)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7033/1645),0,0,(-106/4935)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5243671032720056331580419 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1290 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1287) (section14Witness section14Catalog 1291)) := by
  let l : CertBound := ⟨true,true,⟨⟨(49231/5875),0,0,(-742/17625)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(4009/13690),0,0,(1/13690)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11295827220917134601846938 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1291 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1288) (section14Witness section14Catalog 1292)) := by
  let l : CertBound := ⟨true,true,⟨⟨(5821/1025),0,0,(92/3075)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7711791451991317501349403 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1292 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1289) (section14Witness section14Catalog 1293)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-10743/122617),(832214/367851),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(4840/16393),(-1/16393),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4724707607688329490066470 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1293 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1290) (section14Witness section14Catalog 1294)) := by
  let l : CertBound := ⟨true,false,⟨⟨(2758456/2812381),(4872962/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4952370677105988701136991 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1294 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1291) (section14Witness section14Catalog 1295)) := by
  let l : CertBound := ⟨true,false,⟨⟨(14528/10153),(115045/30459),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11088223549404537318613022 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1295 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1292) (section14Witness section14Catalog 1296)) := by
  let l : CertBound := ⟨true,false,⟨⟨(25229/3290),0,0,(29/1974)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7739/25486),0,0,(1/25486)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10723487089178582805598159 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1296 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1293) (section14Witness section14Catalog 1297)) := by
  let l : CertBound := ⟨true,true,⟨⟨(176603/11750),0,0,(203/7050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(7739/25486),0,0,(1/25486)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (22036266691575846490921709 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1297 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1294) (section14Witness section14Catalog 1298)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22409/2050),0,0,(-107/6150)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (15463955166101059436857886 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1298 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1295) (section14Witness section14Catalog 1299)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-822279/3188042),(40094833/9564126),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(9014/29557),(-1/29557),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9610937669003981615565575 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1299 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1296) (section14Witness section14Catalog 1300)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5019676/2812381),(8939102/2812381),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10047810647513050726323873 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1300 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1297) (section14Witness section14Catalog 1301)) := by
  let l : CertBound := ⟨true,false,⟨⟨(340915/366626),(2173417/1099878),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5426937901346879208095145 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1301 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1298) (section14Witness section14Catalog 1302)) := by
  let l : CertBound := ⟨true,false,⟨⟨(333569/2213857),(4708518/2213857),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1721/6218),(1/18654),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4655067995134808959827032 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1302 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1299) (section14Witness section14Catalog 1303)) := by
  let l : CertBound := ⟨true,false,⟨⟨(6143682/5431127),(26944342/16293381),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4895204746333826965288453 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1303 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1300) (section14Witness section14Catalog 1304)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5252175/856058),0,0,(-340975/856058)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5366611813354167172659561 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1304 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1301) (section14Witness section14Catalog 1305)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1470609/122294),0,0,(-95473/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11531964843124586045650393 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1305 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1302) (section14Witness section14Catalog 1306)) := by
  let l : CertBound := ⟨true,true,⟨⟨(41457/7802),0,0,(667/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7451074159687182229538224 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1306 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1303) (section14Witness section14Catalog 1307)) := by
  let l : CertBound := ⟨true,false,⟨⟨(2890089/4093414),(8630185/4093414),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5390299320714987809017892 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1307 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1304) (section14Witness section14Catalog 1308)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-5694477/24717923),(57954242/24717923),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(10229/38062),(1/38062),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4611057771455958139032977 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1308 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1305) (section14Witness section14Catalog 1309)) := by
  let l : CertBound := ⟨true,false,⟨⟨(16935298/18990023),(33820466/18990023),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4826830729971859283288945 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1309 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1306) (section14Witness section14Catalog 1310)) := by
  let l : CertBound := ⟨true,false,⟨⟨(181841/47558),0,0,(21097/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(8711/32290),0,0,(-1/32290)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5031333793152664064825315 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1310 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1307) (section14Witness section14Catalog 1311)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1272887/169850),0,0,(21097/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(8711/32290),0,0,(-1/32290)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10870033481745519768406163 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1311 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1308) (section14Witness section14Catalog 1312)) := by
  let l : CertBound := ⟨true,true,⟨⟨(171841/25370),0,0,(-4981/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(299/1090),0,0,(-1/1090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7635343021122217313096624 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1312 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1309) (section14Witness section14Catalog 1313)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1415473/4093414),(4117105/4093414),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2059009628603964678651132 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1313 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1310) (section14Witness section14Catalog 1314)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-1726029/24717923),(27246026/24717923),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(1721/6218),(1/18654),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1688747880554947663547393 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1314 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1311) (section14Witness section14Catalog 1315)) := by
  let l : CertBound := ⟨true,false,⟨⟨(8220306/18990023),(48427846/56970069),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(341/1237),(1/1237),0,0⟩,⟨(246/877),(-1/877),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1786967323451819518314254 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1315 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1312) (section14Witness section14Catalog 1316)) := by
  let l : CertBound := ⟨true,false,⟨⟨(89385/47558),0,0,(4225/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1836595685709492491704308 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1316 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1313) (section14Witness section14Catalog 1317)) := by
  let l : CertBound := ⟨true,true,⟨⟨(125139/33970),0,0,(169/6794)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(1403/5030),0,0,(-1/15090)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4608346791156903485088989 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1317 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1314) (section14Witness section14Catalog 1318)) := by
  let l : CertBound := ⟨true,true,⟨⟨(14949/5074),0,0,(-233/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(299/1090),0,0,(1/1090)⟩,⟨(39/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3028353671025523479827946 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1318 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1315) (section14Witness section14Catalog 1319)) := by
  let l : CertBound := ⟨true,false,⟨⟨(150525/183313),(972262/549939),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4811362826942621200309005 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1319 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1316) (section14Witness section14Catalog 1320)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-979217/4427714),(27582493/13283142),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4043726109242293970012696 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1320 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1317) (section14Witness section14Catalog 1321)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5449324/5431127),(24095384/16293381),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4330121271262066614385009 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1321 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1318) (section14Witness section14Catalog 1322)) := by
  let l : CertBound := ⟨true,true,⟨⟨(39343/7802),0,0,(247/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6771920517531194237641618 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1322 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1319) (section14Witness section14Catalog 1323)) := by
  let l : CertBound := ⟨true,false,⟨⟨(249685/61147),0,0,(15340/428029)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (5364973781940431391274032 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1323 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1320) (section14Witness section14Catalog 1324)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2446913/305735),0,0,(21476/305735)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (11528754301553663914134756 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1324 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1321) (section14Witness section14Catalog 1325)) := by
  let l : CertBound := ⟨true,true,⟨⟨(22859/3901),0,0,(98/3901)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7981204888265293312408243 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1325 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1322) (section14Witness section14Catalog 1326)) := by
  let l : CertBound := ⟨true,false,⟨⟨(273375/183313),(1783852/549939),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9780614821096832727292012 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1326 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1323) (section14Witness section14Catalog 1327)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-741808/2213857),(25020023/6641571),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(8222/27073),(1/27073),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8378444479946739681949152 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1327 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1324) (section14Witness section14Catalog 1328)) := by
  let l : CertBound := ⟨true,false,⟨⟨(9931204/5431127),(44192864/16293381),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(469/1549),(1/1549),0,0⟩,⟨(579/1894),(-1/1894),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8891778008389552282567500 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1328 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1325) (section14Witness section14Catalog 1329)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37859/3901),0,0,(-22/3901)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(275/922),0,0,(1/922)⟩,⟨(489/1594),0,0,(-1/1594)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (13686546534805658177973858 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1329 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1326) (section14Witness section14Catalog 1330)) := by
  let l : CertBound := ⟨true,false,⟨⟨(6675455/856058),0,0,(-2935/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10665301779062256455766455 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1330 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1327) (section14Witness section14Catalog 1331)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9345637/611470),0,0,(-28763/611470)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(8531/27970),0,0,(-1/27970)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (21917397175912441040539905 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1331 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1328) (section14Witness section14Catalog 1332)) := by
  let l : CertBound := ⟨true,true,⟨⟨(84343/7802),0,0,(-113/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(313/1042),0,0,(1/1042)⟩,⟨(77/250),0,0,(-1/1750)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (15329932987341741535990040 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1332 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1329) (section14Witness section14Catalog 1333)) := by
  let l : CertBound := ⟨true,false,⟨⟨(621703/2046707),(1842270/2046707),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1763721651614611129823007 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1333 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1330) (section14Witness section14Catalog 1334)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-12835643/49435846),(53625157/49435846),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4264/14557),(1/14557),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1395490540808430667129203 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1334 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1331) (section14Witness section14Catalog 1335)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7266892/18990023),(43323992/56970069),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(237/814),(1/814),0,0⟩,⟨(317/1069),(-1/1069),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1517511587506369483423591 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1335 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1332) (section14Witness section14Catalog 1336)) := by
  let l : CertBound := ⟨true,true,⟨⟨(71399/25370),0,0,(-1809/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(121/430),0,0,(1/430)⟩,⟨(275/922),0,0,(-1/922)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2702697061172821002319877 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1336 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1333) (section14Witness section14Catalog 1337)) := by
  let l : CertBound := ⟨true,false,⟨⟨(33365/23779),0,0,(2628/23779)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1835859277695246338653565 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1337 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1334) (section14Witness section14Catalog 1338)) := by
  let l : CertBound := ⟨true,true,⟨⟨(46711/16985),0,0,(18396/84925)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(655/2218),0,0,(-1/15526)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4606903431448981025109532 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1338 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1335) (section14Witness section14Catalog 1339)) := by
  let l : CertBound := ⟨true,true,⟨⟨(41539/12685),0,0,(-1134/12685)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(313/1042),0,0,(-1/1042)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3282553258764521056023126 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1339 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1336) (section14Witness section14Catalog 1340)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5415/6253),(12589/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(13/23),(1/69),0,0⟩,⟨(59/94),(-1/94),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (7328874094439064268261255 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1340 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1337) (section14Witness section14Catalog 1341)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-28051/75517),(181029/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(732/1249),(1/1249),0,0⟩,⟨(59/94),(-1/94),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6210318950252216551746107 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1341 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1338) (section14Witness section14Catalog 1342)) := by
  let l : CertBound := ⟨true,false,⟨⟨(32140/30251),(51104/30251),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(13/23),(1/69),0,0⟩,⟨(59/94),(-1/94),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6619828570521701793972555 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1342 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1339) (section14Witness section14Catalog 1343)) := by
  let l : CertBound := ⟨true,true,⟨⟨(53/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(15/34),0,0,(1/34)⟩,⟨(53/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (9912610088166446253085301 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1343 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1340) (section14Witness section14Catalog 1344)) := by
  let l : CertBound := ⟨true,false,⟨⟨(783/202),0,0,(251/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(831/1354),0,0,(-1/1354)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (8032355622053559906713341 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 1280).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 1280).take 64 = [⟨1277,[4,8,16],1281⟩,⟨1278,[4,8,16],1282⟩,⟨1279,[4,8,9,12,16],1283⟩,⟨1280,[4,8,9,12,16],1284⟩,⟨1281,[4,8,9,12,16],1285⟩,⟨1282,[4,8,9,12,16],1286⟩,⟨1283,[4,8,9,12,16],1287⟩,⟨1284,[4,8,9,12,16],1288⟩,⟨1285,[4,8,9,12,16],1289⟩,⟨1286,[4,8,9,12,16],1290⟩,⟨1287,[4,8,9,12,16],1291⟩,⟨1288,[4,8,9,12,16],1292⟩,⟨1289,[4,8,9,12,16],1293⟩,⟨1290,[4,8,9,12,16],1294⟩,⟨1291,[4,8,9,12,16],1295⟩,⟨1292,[4,8,9,12,16],1296⟩,⟨1293,[4,8,9,12,16],1297⟩,⟨1294,[4,8,9,12,16],1298⟩,⟨1295,[4,8,9,12,16],1299⟩,⟨1296,[4,8,9,12,16],1300⟩,⟨1297,[4,8,9,12,16],1301⟩,⟨1298,[4,8,9,12,16],1302⟩,⟨1299,[4,8,9,12,16],1303⟩,⟨1300,[4,8,9,12,16],1304⟩,⟨1301,[4,8,9,12,16],1305⟩,⟨1302,[4,8,9,12,16],1306⟩,⟨1303,[4,8,9,12,16],1307⟩,⟨1304,[4,8,9,12,16],1308⟩,⟨1305,[4,8,9,12,16],1309⟩,⟨1306,[4,8,9,12,16],1310⟩,⟨1307,[4,8,9,12,16],1311⟩,⟨1308,[4,8,9,12,16],1312⟩,⟨1309,[4,8,9,12,16],1313⟩,⟨1310,[4,8,9,12,16],1314⟩,⟨1311,[4,8,9,12,16],1315⟩,⟨1312,[4,8,9,12,16],1316⟩,⟨1313,[4,8,9,12,16],1317⟩,⟨1314,[4,8,9,12,16],1318⟩,⟨1315,[4,8,9,12,16],1319⟩,⟨1316,[4,8,9,12,16],1320⟩,⟨1317,[4,8,9,12,16],1321⟩,⟨1318,[4,8,9,12,16],1322⟩,⟨1319,[4,8,9,12,16],1323⟩,⟨1320,[4,8,9,12,16],1324⟩,⟨1321,[4,8,9,12,16],1325⟩,⟨1322,[4,8,9,12,16],1326⟩,⟨1323,[4,8,9,12,16],1327⟩,⟨1324,[4,8,9,12,16],1328⟩,⟨1325,[4,8,9,12,16],1329⟩,⟨1326,[4,8,9,12,16],1330⟩,⟨1327,[4,8,9,12,16],1331⟩,⟨1328,[4,8,9,12,16],1332⟩,⟨1329,[4,8,9,12,16],1333⟩,⟨1330,[4,8,9,12,16],1334⟩,⟨1331,[4,8,9,12,16],1335⟩,⟨1332,[4,8,9,12,16],1336⟩,⟨1333,[4,8,9,12,16],1337⟩,⟨1334,[4,8,9,12,16],1338⟩,⟨1335,[4,8,9,12,16],1339⟩,⟨1336,[4,8,9,12,16],1340⟩,⟨1337,[4,8,9,12,16],1341⟩,⟨1338,[4,8,9,12,16],1342⟩,⟨1339,[4,8,9,12,16],1343⟩,⟨1340,[4,8,9,12,16],1344⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid1280
  · exact valid1281
  · exact valid1282
  · exact valid1283
  · exact valid1284
  · exact valid1285
  · exact valid1286
  · exact valid1287
  · exact valid1288
  · exact valid1289
  · exact valid1290
  · exact valid1291
  · exact valid1292
  · exact valid1293
  · exact valid1294
  · exact valid1295
  · exact valid1296
  · exact valid1297
  · exact valid1298
  · exact valid1299
  · exact valid1300
  · exact valid1301
  · exact valid1302
  · exact valid1303
  · exact valid1304
  · exact valid1305
  · exact valid1306
  · exact valid1307
  · exact valid1308
  · exact valid1309
  · exact valid1310
  · exact valid1311
  · exact valid1312
  · exact valid1313
  · exact valid1314
  · exact valid1315
  · exact valid1316
  · exact valid1317
  · exact valid1318
  · exact valid1319
  · exact valid1320
  · exact valid1321
  · exact valid1322
  · exact valid1323
  · exact valid1324
  · exact valid1325
  · exact valid1326
  · exact valid1327
  · exact valid1328
  · exact valid1329
  · exact valid1330
  · exact valid1331
  · exact valid1332
  · exact valid1333
  · exact valid1334
  · exact valid1335
  · exact valid1336
  · exact valid1337
  · exact valid1338
  · exact valid1339
  · exact valid1340
  · exact valid1341
  · exact valid1342
  · exact valid1343
end Section14Numerical_1280_1344

#print axioms solution
