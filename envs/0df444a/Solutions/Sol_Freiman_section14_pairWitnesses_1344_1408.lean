-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_1344_1408
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:55:48.183773+00:00
-- url     : https://prove2.me/submissions/dd382bc9-3e7e-480d-b9cb-b21197134170

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_1344_1408
private theorem valid1344 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1341) (section14Witness section14Catalog 1345)) := by
  let l : CertBound := ⟨true,true,⟨⟨(38367/5050),0,0,(1757/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(831/1354),0,0,(-1/1354)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (16832493568644541209364978 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1345 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1342) (section14Witness section14Catalog 1346)) := by
  let l : CertBound := ⟨true,true,⟨⟨(63/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/2),0,0,(1/42)⟩,⟨(63/94),0,0,(-1/94)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (12151212709700423882852884 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1346 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1343) (section14Witness section14Catalog 1347)) := by
  let l : CertBound := ⟨true,false,⟨⟨(55/169),(121/169),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2082227839886363555208953 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1347 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1344) (section14Witness section14Catalog 1348)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5313/75517),(57277/75517),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(113/179),(1/537),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1704181932940263820073682 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1348 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1345) (section14Witness section14Catalog 1349)) := by
  let l : CertBound := ⟨true,false,⟨⟨(11860/30251),(54616/90753),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1812651973575796877375381 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1349 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1346) (section14Witness section14Catalog 1350)) := by
  let l : CertBound := ⟨true,false,⟨⟨(2697/1414),0,0,(-19/202)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1944246010274573784160962 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1350 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1347) (section14Witness section14Catalog 1351)) := by
  let l : CertBound := ⟨true,true,⟨⟨(18879/5050),0,0,(-931/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4899798729557728409162314 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1351 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1348) (section14Witness section14Catalog 1352)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3027102412609993563486529 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1352 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1349) (section14Witness section14Catalog 1353)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1064/6539),(2138/6539),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(17/22),(-1/22),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (430252265706797275417176 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1353 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1350) (section14Witness section14Catalog 1354)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (422208168385664214414884 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1354 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1351) (section14Witness section14Catalog 1355)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(95/134),0,0,(-1/402)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1852188201079182234774137 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1355 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1352) (section14Witness section14Catalog 1356)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(19/34),0,0,(1/34)⟩,⟨(3/2),0,0,(-1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1057532765567776170550298 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1356 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1353) (section14Witness section14Catalog 1357)) := by
  let l : CertBound := ⟨true,true,⟨⟨(232647/289822),(279009/289822),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2744358222669033750467886 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1357 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1354) (section14Witness section14Catalog 1358)) := by
  let l : CertBound := ⟨true,true,⟨⟨(511868/663637),(641519/663637),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2705207317468687621362599 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1358 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1355) (section14Witness section14Catalog 1359)) := by
  let l : CertBound := ⟨true,true,⟨⟨(23933/11750),0,0,(9443/35250)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3885321548550198446226582 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1359 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1356) (section14Witness section14Catalog 1360)) := by
  let l : CertBound := ⟨true,true,⟨⟨(97/50),0,0,(19/150)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2752200504385887000683386 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1360 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1357) (section14Witness section14Catalog 1361)) := by
  let l : CertBound := ⟨true,true,⟨⟨(100785/395044),(447849/395044),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2363335224277681791407014 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1361 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1358) (section14Witness section14Catalog 1362)) := by
  let l : CertBound := ⟨true,true,⟨⟨(200001/1197131),(1404324/1197131),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(66/179),(-1/537),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2331532493461591980371726 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1362 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1359) (section14Witness section14Catalog 1363)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2457/1010),0,0,(217/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4327609437670060469780105 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1363 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1360) (section14Witness section14Catalog 1364)) := by
  let l : CertBound := ⟨true,true,⟨⟨(21/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3024602021908053546108121 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1364 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1361) (section14Witness section14Catalog 1365)) := by
  let l : CertBound := ⟨true,true,⟨⟨(819/850),0,0,(-217/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-77549/206349),(31001/68783),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (276619175825674051545330 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1365 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1362) (section14Witness section14Catalog 1366)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-67190/998283),(99522/332761),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (265191506331260315503477 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1366 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1363) (section14Witness section14Catalog 1367)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-2642/11147),(9871/11147),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (907349252279206540759561 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1367 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1364) (section14Witness section14Catalog 1368)) := by
  let l : CertBound := ⟨true,false,⟨⟨(3419/3290),0,0,(1349/9870)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1462800791716517476672074 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1368 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1365) (section14Witness section14Catalog 1369)) := by
  let l : CertBound := ⟨true,true,⟨⟨(551/1846),(1285/1846),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1221605689834861913670598 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1369 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1366) (section14Witness section14Catalog 1370)) := by
  let l : CertBound := ⟨true,true,⟨⟨(91401/255671),(150247/255671),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1026165367751817142475140 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1370 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1367) (section14Witness section14Catalog 1371)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2497/2050),0,0,(273/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1724206981758906487774830 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1371 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1368) (section14Witness section14Catalog 1372)) := by
  let l : CertBound := ⟨true,true,⟨⟨(134765/220597),(599154/2426567),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (507637958628219169896465 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1372 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1369) (section14Witness section14Catalog 1373)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2210439/593885),0,0,(-66752/118777)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (680818419717066434631349 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1373 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1370) (section14Witness section14Catalog 1374)) := by
  let l : CertBound := ⟨true,true,⟨⟨(476376/728233),(1155575/5097631),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (519649669014579093067740 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1374 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1371) (section14Witness section14Catalog 1375)) := by
  let l : CertBound := ⟨true,true,⟨⟨(572469/385801),(1283338/1157403),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3993996093258781323739106 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1375 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1372) (section14Witness section14Catalog 1376)) := by
  let l : CertBound := ⟨true,true,⟨⟨(11168191/9318578),(29141215/27955734),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3401523113724802886318483 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1376 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1373) (section14Witness section14Catalog 1377)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1856617/611470),0,0,(14189/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4243000828293077023861529 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1377 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1374) (section14Witness section14Catalog 1378)) := by
  let l : CertBound := ⟨true,true,⟨⟨(30479290/17975711),(14199909/17975711),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3489518064470214586149894 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1378 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1375) (section14Witness section14Catalog 1379)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (427876593697690022407127 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1379 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1376) (section14Witness section14Catalog 1380)) := by
  let l : CertBound := ⟨true,true,⟨⟨(184891/169850),0,0,(19107/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1331455108211710217504239 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1380 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1377) (section14Witness section14Catalog 1381)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32927/25370),0,0,(-297/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (799579284461600313242543 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1381 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1378) (section14Witness section14Catalog 1382)) := by
  let l : CertBound := ⟨true,true,⟨⟨(70901/157942),(68551/157942),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (749083018788592636272752 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1382 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1379) (section14Witness section14Catalog 1383)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3919/6539),(2946/6539),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1016372551725425176697613 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1383 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1380) (section14Witness section14Catalog 1384)) := by
  let l : CertBound := ⟨true,true,⟨⟨(12379410/17975711),(5738981/17975711),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (809750228812226028156653 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1384 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1381) (section14Witness section14Catalog 1385)) := by
  let l : CertBound := ⟨true,true,⟨⟨(238689/2213857),(4142842/6641571),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (749504224121538364477812 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1385 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1382) (section14Witness section14Catalog 1386)) := by
  let l : CertBound := ⟨true,true,⟨⟨(111595/366626),(219483/366626),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (982389533904603059737673 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1386 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1383) (section14Witness section14Catalog 1387)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1960594/5431127),(2728898/5431127),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (815213627412349100578647 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1387 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1384) (section14Witness section14Catalog 1388)) := by
  let l : CertBound := ⟨true,false,⟨⟨(253425/122294),0,0,(-149815/856058)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (877358881850214151205661 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1388 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1385) (section14Witness section14Catalog 1389)) := by
  let l : CertBound := ⟨true,true,⟨⟨(496713/122294),0,0,(-209741/611470)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2733029097376838123600750 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1389 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1386) (section14Witness section14Catalog 1390)) := by
  let l : CertBound := ⟨true,true,⟨⟨(8457/7802),0,0,(931/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1431229984494359362842828 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1390 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1387) (section14Witness section14Catalog 1391)) := by
  let l : CertBound := ⟨true,true,⟨⟨(950149/771602),(703311/771602),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3214398343426582011022834 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1391 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1388) (section14Witness section14Catalog 1392)) := by
  let l : CertBound := ⟨true,true,⟨⟨(4064450/4659289),(4170517/4659289),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2627288815486376110960745 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1392 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1389) (section14Witness section14Catalog 1393)) := by
  let l : CertBound := ⟨true,true,⟨⟨(50142285/35951422),(23544709/35951422),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2787904530854797460539605 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1393 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1390) (section14Witness section14Catalog 1394)) := by
  let l : CertBound := ⟨true,true,⟨⟨(189609/785686),(191283/785686),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(3/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (20545966466563013309299 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1394 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1390) (section14Witness section14Catalog 1395)) := by
  let l : CertBound := ⟨true,true,⟨⟨(189609/785686),(191283/785686),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/3),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (17673927701299590142983 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1395 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1391) (section14Witness section14Catalog 1396)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (89666697783936132066100 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1396 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1392) (section14Witness section14Catalog 1397)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1503594694362958683607152 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1397 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1393) (section14Witness section14Catalog 1398)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/2),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (824440065828471907680876 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1398 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1394) (section14Witness section14Catalog 1399)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (417877294506014503345535 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1399 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1395) (section14Witness section14Catalog 1400)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (321076318677667503554902 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1400 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1396) (section14Witness section14Catalog 1401)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(3/407),(2/37),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨2,-1,0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (239503768433942455413530 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1401 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1397) (section14Witness section14Catalog 1402)) := by
  let l : CertBound := ⟨true,false,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (26620193537223885152906 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1402 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1398) (section14Witness section14Catalog 1403)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(161/500),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,-1,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (10038539081693823861312 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1403 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1399) (section14Witness section14Catalog 1404)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1/235),0,0,(16/4935)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (657506080537080333151244 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1404 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1400) (section14Witness section14Catalog 1405)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/1025),0,0,(28/3075)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (636533892431317924750930 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1405 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1401) (section14Witness section14Catalog 1406)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1043/46079),(1720/46079),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (611297411341296823216806 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1406 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1402) (section14Witness section14Catalog 1407)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(49/5875),0,0,(112/17625)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (617778922906255806533133 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid1407 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 1403) (section14Witness section14Catalog 1408)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-5195/108914),(2926/54457),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(1/2),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (604008409587794943705790 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 1344).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 1344).take 64 = [⟨1341,[4,8,9,12,16],1345⟩,⟨1342,[4,8,9,12,16],1346⟩,⟨1343,[4,8,9,12,16],1347⟩,⟨1344,[4,8,9,12,16],1348⟩,⟨1345,[4,8,9,12,16],1349⟩,⟨1346,[4,8,9,12,16],1350⟩,⟨1347,[4,8,9,12,16],1351⟩,⟨1348,[4,8,9,12,16],1352⟩,⟨1349,[4,8,9,12],1353⟩,⟨1350,[4,8,9,12],1354⟩,⟨1351,[4,8,9,12],1355⟩,⟨1352,[4,8,9,12],1356⟩,⟨1353,[4,8,9,12,16],1357⟩,⟨1354,[4,8,9,12,16],1358⟩,⟨1355,[4,8,9,12,16],1359⟩,⟨1356,[4,8,9,12,16],1360⟩,⟨1357,[4,8,9,12,16],1361⟩,⟨1358,[4,8,9,12,16],1362⟩,⟨1359,[4,8,9,12,16],1363⟩,⟨1360,[4,8,9,12,16],1364⟩,⟨1361,[4,5,10,16],1365⟩,⟨1362,[4,5,8,9,12,16],1366⟩,⟨1363,[4,8,9,12,16],1367⟩,⟨1364,[4,8,9,12,16],1368⟩,⟨1365,[4,8,9,12,16],1369⟩,⟨1366,[4,8,9,12,16],1370⟩,⟨1367,[4,8,9,12,16],1371⟩,⟨1368,[4,8,9,12,16],1372⟩,⟨1369,[4,8,9,12,16],1373⟩,⟨1370,[4,8,9,12,16],1374⟩,⟨1371,[4,8,9,12,16],1375⟩,⟨1372,[4,8,9,12,16],1376⟩,⟨1373,[4,8,9,12,16],1377⟩,⟨1374,[4,8,9,12,16],1378⟩,⟨1375,[4,5,8,9,12,16],1379⟩,⟨1376,[4,8,9,12,16],1380⟩,⟨1377,[4,8,9,12,16],1381⟩,⟨1378,[4,8,9,12,16],1382⟩,⟨1379,[4,8,9,12,16],1383⟩,⟨1380,[4,8,9,12,16],1384⟩,⟨1381,[4,8,9,12,16],1385⟩,⟨1382,[4,8,9,12,16],1386⟩,⟨1383,[4,8,9,12,16],1387⟩,⟨1384,[4,8,9,12,16],1388⟩,⟨1385,[4,8,9,12,16],1389⟩,⟨1386,[4,8,9,12,16],1390⟩,⟨1387,[4,8,9,12,16],1391⟩,⟨1388,[4,8,9,12,16],1392⟩,⟨1389,[4,8,9,12,16],1393⟩,⟨1390,[4,8,12,16],1394⟩,⟨1390,[9],1395⟩,⟨1391,[4,8,9,12,16],1396⟩,⟨1392,[4,8,9,12,16],1397⟩,⟨1393,[4,8,9,12,16],1398⟩,⟨1394,[5,6],1399⟩,⟨1395,[5,6],1400⟩,⟨1396,[5,9,10],1401⟩,⟨1397,[5,6,9,10],1402⟩,⟨1398,[5,6,7,8,9,10,12],1403⟩,⟨1399,[5,6,8,9,10,12],1404⟩,⟨1400,[5,6,8,9,10,12],1405⟩,⟨1401,[5,6,8,9,10,12],1406⟩,⟨1402,[5,6,8,9,10,12],1407⟩,⟨1403,[5,6,8,9,10,12],1408⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid1344
  · exact valid1345
  · exact valid1346
  · exact valid1347
  · exact valid1348
  · exact valid1349
  · exact valid1350
  · exact valid1351
  · exact valid1352
  · exact valid1353
  · exact valid1354
  · exact valid1355
  · exact valid1356
  · exact valid1357
  · exact valid1358
  · exact valid1359
  · exact valid1360
  · exact valid1361
  · exact valid1362
  · exact valid1363
  · exact valid1364
  · exact valid1365
  · exact valid1366
  · exact valid1367
  · exact valid1368
  · exact valid1369
  · exact valid1370
  · exact valid1371
  · exact valid1372
  · exact valid1373
  · exact valid1374
  · exact valid1375
  · exact valid1376
  · exact valid1377
  · exact valid1378
  · exact valid1379
  · exact valid1380
  · exact valid1381
  · exact valid1382
  · exact valid1383
  · exact valid1384
  · exact valid1385
  · exact valid1386
  · exact valid1387
  · exact valid1388
  · exact valid1389
  · exact valid1390
  · exact valid1391
  · exact valid1392
  · exact valid1393
  · exact valid1394
  · exact valid1395
  · exact valid1396
  · exact valid1397
  · exact valid1398
  · exact valid1399
  · exact valid1400
  · exact valid1401
  · exact valid1402
  · exact valid1403
  · exact valid1404
  · exact valid1405
  · exact valid1406
  · exact valid1407
end Section14Numerical_1344_1408

#print axioms solution
