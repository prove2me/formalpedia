-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_0832_0896
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:27:01.810384+00:00
-- url     : https://prove2.me/submissions/7062c761-90fb-405f-b442-0b5cfd2e811d

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_832_896
private theorem valid832 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 832) (section14Witness section14Catalog 833)) := by
  let l : CertBound := ⟨true,true,⟨⟨(527723/557594),0,0,(149891/2787970)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(17472/11581),(-8957/11581),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1349317455986738782331637 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid833 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 833) (section14Witness section14Catalog 834)) := by
  let l : CertBound := ⟨true,true,⟨⟨(6927/7802),0,0,(7/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(91869291/82005061),(-43969063/82005061),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (921416778061550442246404 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid834 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 834) (section14Witness section14Catalog 835)) := by
  let l : CertBound := ⟨true,false,⟨⟨(26413/47558),0,0,(19107/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(63314355/72113948),(-29352973/72113948),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (840034313220269082024584 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid835 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 835) (section14Witness section14Catalog 836)) := by
  let l : CertBound := ⟨true,false,⟨⟨(26413/47558),0,0,(19107/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(307006995/495446761),(-379202132/1486340283),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (833786403688983905948313 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid836 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 836) (section14Witness section14Catalog 837)) := by
  let l : CertBound := ⟨true,true,⟨⟨(527723/557594),0,0,(149891/2787970)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(63314355/72113948),(-29352973/72113948),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1344178648647064677687946 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid837 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 837) (section14Witness section14Catalog 838)) := by
  let l : CertBound := ⟨true,true,⟨⟨(6927/7802),0,0,(7/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(50343/75433),(-41057/150866),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (915584637373728209166600 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid838 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 838) (section14Witness section14Catalog 839)) := by
  let l : CertBound := ⟨true,true,⟨⟨(184891/169850),0,0,(19107/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(17472/11581),(-8957/11581),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1868950420394464880186560 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid839 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 839) (section14Witness section14Catalog 840)) := by
  let l : CertBound := ⟨true,true,⟨⟨(184891/169850),0,0,(19107/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(127151/150866),(-58285/150866),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1862986101404045516627188 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid840 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 840) (section14Witness section14Catalog 841)) := by
  let l : CertBound := ⟨true,true,⟨⟨(184891/169850),0,0,(19107/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(91869291/82005061),(-43969063/82005061),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1839712777677491139793864 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid841 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 841) (section14Witness section14Catalog 842)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32927/25370),0,0,(-297/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(193815/218041),(-87328/218041),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1366655049365728545527397 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid842 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 842) (section14Witness section14Catalog 843)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32927/25370),0,0,(-297/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1477831/2840426),(-524463/2840426),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1359774033421947966378182 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid843 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 843) (section14Witness section14Catalog 844)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32927/25370),0,0,(-297/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(772750014/1543948321),(-252072474/1543948321),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1337379658691020695490855 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid844 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 844) (section14Witness section14Catalog 845)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3919/6539),(2946/6539),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(637825/1834546),0,0,(-244715/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1614757159328507971641312 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid845 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 845) (section14Witness section14Catalog 846)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2207202/4659289),(5960815/13977867),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9141/24898),0,0,(-2839/74694)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1332227361293824456245626 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid846 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 846) (section14Witness section14Catalog 847)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3919/6539),(2946/6539),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7109/12685),0,0,(-224/12685)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1177989338142206825279532 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid847 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 847) (section14Witness section14Catalog 848)) := by
  let l : CertBound := ⟨true,true,⟨⟨(37181/60671),(25893/60671),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(178591/262078),0,0,(-342601/3931170)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1397946106161398385475337 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid848 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 848) (section14Witness section14Catalog 849)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3919/6539),(2946/6539),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(16125/18214),0,0,(-125/2602)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (939954464748147070104528 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid849 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 849) (section14Witness section14Catalog 850)) := by
  let l : CertBound := ⟨true,true,⟨⟨(70901/157942),(68551/157942),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(637825/1834546),0,0,(-244715/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1381360299665649180194745 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid850 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 850) (section14Witness section14Catalog 851)) := by
  let l : CertBound := ⟨true,true,⟨⟨(8149129/38105268),(18877421/38105268),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9141/24898),0,0,(-2839/74694)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1149192448883089098538203 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid851 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 851) (section14Witness section14Catalog 852)) := by
  let l : CertBound := ⟨true,true,⟨⟨(70901/157942),(68551/157942),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7109/12685),0,0,(-224/12685)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (944430622866965523097960 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid852 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 852) (section14Witness section14Catalog 853)) := by
  let l : CertBound := ⟨true,true,⟨⟨(353603/732719),(293596/732719),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(178591/262078),0,0,(-342601/3931170)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1169224098770373695507293 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid853 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 853) (section14Witness section14Catalog 854)) := by
  let l : CertBound := ⟨true,true,⟨⟨(70901/157942),(68551/157942),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (707782373174404428309178 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid854 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 854) (section14Witness section14Catalog 855)) := by
  let l : CertBound := ⟨true,true,⟨⟨(4515/2602),0,0,(-245/2602)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9141/24898),0,0,(-2839/74694)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1455457018591273610935859 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid855 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 855) (section14Witness section14Catalog 856)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3919/6539),(2946/6539),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (950665482833258491597121 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid856 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 856) (section14Witness section14Catalog 857)) := by
  let l : CertBound := ⟨true,true,⟨⟨(12379410/17975711),(5738981/17975711),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(637825/1834546),0,0,(-244715/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1434463099841500443529716 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid857 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 857) (section14Witness section14Catalog 858)) := by
  let l : CertBound := ⟨true,true,⟨⟨(50923/78971),(20346/78971),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9141/24898),0,0,(-2839/74694)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1173832963005124222968441 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid858 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 858) (section14Witness section14Catalog 859)) := by
  let l : CertBound := ⟨true,true,⟨⟨(12379410/17975711),(5738981/17975711),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7109/12685),0,0,(-224/12685)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (997706435925338386088729 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid859 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 859) (section14Witness section14Catalog 860)) := by
  let l : CertBound := ⟨true,true,⟨⟨(117112300/166784579),(49286960/166784579),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(178591/262078),0,0,(-342601/3931170)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1217708245618049754925344 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid860 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 860) (section14Witness section14Catalog 861)) := by
  let l : CertBound := ⟨true,true,⟨⟨(12379410/17975711),(5738981/17975711),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (763270449690952807130961 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid861 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 861) (section14Witness section14Catalog 862)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-5827030/5460911),(12492497/16382733),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (453650862757355771608594 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid862 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 862) (section14Witness section14Catalog 863)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7199737/6882244),(-7612151/17205610),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (416976013866843431300007 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid863 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 863) (section14Witness section14Catalog 864)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3675/6794),0,0,(67/6794)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-5827030/5460911),(12492497/16382733),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (435593746849841214323845 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid864 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 864) (section14Witness section14Catalog 865)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-748551/1448101),(2031182/4344303),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (398707727262161198170352 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid865 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 865) (section14Witness section14Catalog 866)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(24122/44759),(-22358/134277),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (446687517912134842902437 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid866 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 866) (section14Witness section14Catalog 867)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1295924/2569417),(-375018/2569417),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (445004778057002903832260 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid867 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 867) (section14Witness section14Catalog 868)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3675/6794),0,0,(67/6794)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(24122/44759),(-22358/134277),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (429216430090668522917297 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid868 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 868) (section14Witness section14Catalog 869)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(6155/11869),(-1825/11869),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (443974747150416564249209 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid869 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 869) (section14Witness section14Catalog 870)) := by
  let l : CertBound := ⟨true,true,⟨⟨(189609/785686),(191283/785686),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(739135/1834546),0,0,(-108575/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (496962785529087553848953 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid870 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 870) (section14Witness section14Catalog 871)) := by
  let l : CertBound := ⟨true,true,⟨⟨(440576/1840477),(448511/1840477),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2523/5074),0,0,(-77/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (338735393902818393488823 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid871 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 871) (section14Witness section14Catalog 872)) := by
  let l : CertBound := ⟨true,true,⟨⟨(68287/280379),(67736/280379),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1034789/1310390),0,0,(-30401/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (33694755556316539042647 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid872 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 872) (section14Witness section14Catalog 873)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(11/210)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (658114387780214733216413 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid873 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 873) (section14Witness section14Catalog 874)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/17),0,0,(4/51)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (510739797387589803924463 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid874 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 874) (section14Witness section14Catalog 875)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-54/407),(85/407),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (479067687601355214164901 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid875 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 875) (section14Witness section14Catalog 876)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1455/5291),(3191/10582),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (443795901463098605789625 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid876 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 876) (section14Witness section14Catalog 877)) := by
  let l : CertBound := ⟨true,true,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (705079490583648185783171 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid877 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 877) (section14Witness section14Catalog 878)) := by
  let l : CertBound := ⟨true,true,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(11/210)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (638496156795916050008222 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid878 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 878) (section14Witness section14Catalog 879)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/2),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4552648737192059791832 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid879 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 878) (section14Witness section14Catalog 880)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(3/4),(4/5),(1/4),(1/3)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (127746844915240390295431 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid880 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 879) (section14Witness section14Catalog 881)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(343/5050),0,0,(413/5050)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (22121793467217945548432 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid881 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 880) (section14Witness section14Catalog 882)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (499442333071884445878714 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid882 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 881) (section14Witness section14Catalog 883)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (811689716602617161972743 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid883 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 882) (section14Witness section14Catalog 884)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (851665756026668633963281 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid884 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 883) (section14Witness section14Catalog 885)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (741355150058288138469920 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid885 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 884) (section14Witness section14Catalog 886)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (698563348147253831018131 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid886 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 885) (section14Witness section14Catalog 887)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (665430629439291096006775 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid887 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 886) (section14Witness section14Catalog 888)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (684746612985515491632177 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid888 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 887) (section14Witness section14Catalog 889)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (438306849360441555155615 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid889 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 888) (section14Witness section14Catalog 890)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1/2),(5/6),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1844486444583577226973502 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid890 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 889) (section14Witness section14Catalog 891)) := by
  let l : CertBound := ⟨true,false,⟨⟨(65/107),(221/321),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1590372259851038679748251 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid891 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 890) (section14Witness section14Catalog 892)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2905281170144044419985007 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid892 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 891) (section14Witness section14Catalog 893)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-1/2),0,0,(59/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2408789373055842986732398 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid893 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 892) (section14Witness section14Catalog 894)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-49/50),0,0,(59/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (6247564151189323638926193 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid894 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 893) (section14Witness section14Catalog 895)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1/2),0,0,(1/2)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(37/50),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩,⟨(52/73),(1/73),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3520224319657167409757631 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid895 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 894) (section14Witness section14Catalog 896)) := by
  let l : CertBound := ⟨true,false,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (505357606078626134242971 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 832).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 832).take 64 = [⟨832,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],833⟩,⟨833,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],834⟩,⟨834,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],835⟩,⟨835,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],836⟩,⟨836,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],837⟩,⟨837,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],838⟩,⟨838,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],839⟩,⟨839,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],840⟩,⟨840,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],841⟩,⟨841,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],842⟩,⟨842,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],843⟩,⟨843,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],844⟩,⟨844,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],845⟩,⟨845,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],846⟩,⟨846,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],847⟩,⟨847,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],848⟩,⟨848,[1,4,5,6,8,9,10,11,12,13,16],849⟩,⟨849,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],850⟩,⟨850,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],851⟩,⟨851,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],852⟩,⟨852,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],853⟩,⟨853,[1,2,3,5,6,7,10,11,13,14,15],854⟩,⟨854,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],855⟩,⟨855,[1,2,3,5,6,7,10,11,13,14,15],856⟩,⟨856,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],857⟩,⟨857,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],858⟩,⟨858,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],859⟩,⟨859,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],860⟩,⟨860,[1,2,3,5,6,7,10,11,13,14,15],861⟩,⟨861,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],862⟩,⟨862,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],863⟩,⟨863,[1,2,3,6,7,10,11,13,14,15],864⟩,⟨864,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],865⟩,⟨865,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],866⟩,⟨866,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],867⟩,⟨867,[1,2,3,6,7,10,11,13,14,15],868⟩,⟨868,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],869⟩,⟨869,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],870⟩,⟨870,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],871⟩,⟨871,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],872⟩,⟨872,[1,2,4,5,6,8,9,10,12,13,14,16],873⟩,⟨873,[1,2,3,4,5,6,7,8,9,10,11,12],874⟩,⟨874,[1,2,4,5,6,8,9,10,12],875⟩,⟨875,[1,2,4,5,6,8,9,10,12],876⟩,⟨876,[1,2,4,5,6,8,9,10,12],877⟩,⟨877,[1,2,4,5,6,8,9,10,12],878⟩,⟨878,[1,2,13,14],879⟩,⟨878,[15],880⟩,⟨879,[1,2,4,5,6,8,9,10,12,13,14,16],881⟩,⟨880,[1,2,3,5,6,7,9,10,11,13,14,15],882⟩,⟨881,[1,2,3,5,6,7,9,10,11,13,14,15],883⟩,⟨882,[1,2,4,5,6,8,9,10,12,13,14,16],884⟩,⟨883,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],885⟩,⟨884,[1,2,4,5,6,8,9,10,12,13,14,16],886⟩,⟨885,[1,2,3,5,6,7,13,14,15],887⟩,⟨886,[1,2,4,5,6,8,9,10,12,13,14,16],888⟩,⟨887,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],889⟩,⟨888,[1,2,3,4,5,6,7,8,13,14,15,16],890⟩,⟨889,[1,2,3,4,5,6,7,8,13,14,15,16],891⟩,⟨890,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],892⟩,⟨891,[1,2,3,4,5,6,7,8,13,14,15,16],893⟩,⟨892,[1,2,3,4,5,6,7,8,13,14,15,16],894⟩,⟨893,[1,2,3,4,5,6,7,8,13,14,15,16],895⟩,⟨894,[1,2,4,5,6,8,9,10,13,14,16],896⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid832
  · exact valid833
  · exact valid834
  · exact valid835
  · exact valid836
  · exact valid837
  · exact valid838
  · exact valid839
  · exact valid840
  · exact valid841
  · exact valid842
  · exact valid843
  · exact valid844
  · exact valid845
  · exact valid846
  · exact valid847
  · exact valid848
  · exact valid849
  · exact valid850
  · exact valid851
  · exact valid852
  · exact valid853
  · exact valid854
  · exact valid855
  · exact valid856
  · exact valid857
  · exact valid858
  · exact valid859
  · exact valid860
  · exact valid861
  · exact valid862
  · exact valid863
  · exact valid864
  · exact valid865
  · exact valid866
  · exact valid867
  · exact valid868
  · exact valid869
  · exact valid870
  · exact valid871
  · exact valid872
  · exact valid873
  · exact valid874
  · exact valid875
  · exact valid876
  · exact valid877
  · exact valid878
  · exact valid879
  · exact valid880
  · exact valid881
  · exact valid882
  · exact valid883
  · exact valid884
  · exact valid885
  · exact valid886
  · exact valid887
  · exact valid888
  · exact valid889
  · exact valid890
  · exact valid891
  · exact valid892
  · exact valid893
  · exact valid894
  · exact valid895
end Section14Numerical_832_896

#print axioms solution
