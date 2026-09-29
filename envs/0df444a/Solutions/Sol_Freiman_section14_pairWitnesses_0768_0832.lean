-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_0768_0832
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:17:44.779254+00:00
-- url     : https://prove2.me/submissions/5bbfc174-9366-4b21-b825-77bd9a9a0c2f

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_768_832
private theorem valid768 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 768) (section14Witness section14Catalog 769)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(20605417/16123461),(-9037402/16123461),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (908879032131302242070782 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid769 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 769) (section14Witness section14Catalog 770)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1326155/856058),0,0,(50675/856058)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(620769681/592668098),(-754595851/1778004294),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1975200499911180366306662 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid770 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 770) (section14Witness section14Catalog 771)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2497/2050),0,0,(273/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(620769681/592668098),(-754595851/1778004294),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2016397006620320690913039 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid771 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 771) (section14Witness section14Catalog 772)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1856617/611470),0,0,(14189/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(20605417/16123461),(-9037402/16123461),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4273358361454091792246639 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid772 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 772) (section14Witness section14Catalog 773)) := by
  let l : CertBound := ⟨true,true,⟨⟨(221/94),0,0,(5/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(236157902/250414657),(-257435723/751243971),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2942898815841039220606378 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid773 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 773) (section14Witness section14Catalog 774)) := by
  let l : CertBound := ⟨true,true,⟨⟨(572469/385801),(1283338/1157403),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(357775/262078),0,0,(-1255075/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4004984500841983022761845 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid774 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 774) (section14Witness section14Catalog 775)) := by
  let l : CertBound := ⟨true,true,⟨⟨(5039018/4659289),(15070079/13977867),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(263/422),0,0,(-61/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3307092063275555576207000 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid775 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 775) (section14Witness section14Catalog 776)) := by
  let l : CertBound := ⟨true,true,⟨⟨(572469/385801),(1283338/1157403),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3675777427694292957012959 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid776 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 776) (section14Witness section14Catalog 777)) := by
  let l : CertBound := ⟨true,true,⟨⟨(5425431/3579589),(11287229/10738767),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(701239/262078),0,0,(-351421/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3516382043896620880620396 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid777 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 777) (section14Witness section14Catalog 778)) := by
  let l : CertBound := ⟨true,true,⟨⟨(11168191/9318578),(29141215/27955734),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(357775/262078),0,0,(-1255075/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3485450869104164655176658 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid778 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 778) (section14Witness section14Catalog 779)) := by
  let l : CertBound := ⟨true,true,⟨⟨(20116081/38105268),(46547189/38105268),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(263/422),0,0,(-61/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2911052351275434063229365 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid779 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 779) (section14Witness section14Catalog 780)) := by
  let l : CertBound := ⟨true,true,⟨⟨(11168191/9318578),(29141215/27955734),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3135127719591473843356315 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid780 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 780) (section14Witness section14Catalog 781)) := by
  let l : CertBound := ⟨true,true,⟨⟨(54471145/43230421),(126078268/129691263),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(701239/262078),0,0,(-351421/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3007254477528028453339344 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid781 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 781) (section14Witness section14Catalog 782)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1856617/611470),0,0,(14189/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(357775/262078),0,0,(-1255075/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4220744534003186402494191 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid782 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 782) (section14Witness section14Catalog 783)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1856617/611470),0,0,(14189/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(263/422),0,0,(-61/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (4114853312375021389141049 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid783 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 783) (section14Witness section14Catalog 784)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1856617/611470),0,0,(14189/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3898831788531197817946014 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid784 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 784) (section14Witness section14Catalog 785)) := by
  let l : CertBound := ⟨true,true,⟨⟨(1856617/611470),0,0,(14189/122294)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(701239/262078),0,0,(-351421/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3819557610333542059386619 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid785 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 785) (section14Witness section14Catalog 786)) := by
  let l : CertBound := ⟨true,true,⟨⟨(30479290/17975711),(14199909/17975711),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(357775/262078),0,0,(-1255075/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3562811628487548791932290 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid786 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 786) (section14Witness section14Catalog 787)) := by
  let l : CertBound := ⟨true,true,⟨⟨(352019471/217091279),(129396314/217091279),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(263/422),0,0,(-61/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2924082039825998609215840 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid787 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 787) (section14Witness section14Catalog 788)) := by
  let l : CertBound := ⟨true,true,⟨⟨(30479290/17975711),(14199909/17975711),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3215785764855813019780814 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid788 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 788) (section14Witness section14Catalog 789)) := by
  let l : CertBound := ⟨true,true,⟨⟨(288102700/166784579),(366366320/500353737),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(701239/262078),0,0,(-351421/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3074333587413665942755772 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid789 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 789) (section14Witness section14Catalog 790)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (420482428343346177355652 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid790 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 790) (section14Witness section14Catalog 791)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(30479290/18028487),(-14199909/18028487),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (357194603872788844564704 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid791 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 791) (section14Witness section14Catalog 792)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1717407/1720561),(1283338/1720561),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (402226501542658806591528 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid792 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 792) (section14Witness section14Catalog 793)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-33504573/50976119),(29141215/50976119),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (348158802260585194811318 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid793 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 793) (section14Witness section14Catalog 794)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1717407/1720561),(1283338/1720561),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (921352373142227270088171 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid794 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 794) (section14Witness section14Catalog 795)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (935324933427135761651887 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid795 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 795) (section14Witness section14Catalog 796)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(30479290/18028487),(-14199909/18028487),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (875307149440277617068162 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid796 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 796) (section14Witness section14Catalog 797)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1717407/1720561),(1283338/1720561),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (917642707447830323998651 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid797 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 797) (section14Witness section14Catalog 798)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-33504573/50976119),(29141215/50976119),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (866878143833445127089758 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid798 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 798) (section14Witness section14Catalog 799)) := by
  let l : CertBound := ⟨true,false,⟨⟨(42933/47558),0,0,(50203/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1706181090315384252390311 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid799 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 799) (section14Witness section14Catalog 800)) := by
  let l : CertBound := ⟨true,false,⟨⟨(42933/47558),0,0,(50203/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(8643081/6882244),(-4579579/8602805),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1635688972668993905068063 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid800 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 800) (section14Witness section14Catalog 801)) := by
  let l : CertBound := ⟨true,false,⟨⟨(42933/47558),0,0,(50203/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-16276293/10921822),(11287229/10921822),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1679907701075398491008796 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid801 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 801) (section14Witness section14Catalog 802)) := by
  let l : CertBound := ⟨true,false,⟨⟨(42933/47558),0,0,(50203/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-163413435/161793769),(126078268/161793769),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1628158888189773628195720 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid802 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 802) (section14Witness section14Catalog 803)) := by
  let l : CertBound := ⟨true,true,⟨⟨(300531/169850),0,0,(50203/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3695363778075131730622333 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid803 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 803) (section14Witness section14Catalog 804)) := by
  let l : CertBound := ⟨true,true,⟨⟨(300531/169850),0,0,(50203/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(30479290/18028487),(-14199909/18028487),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3632652579383615498493184 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid804 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 804) (section14Witness section14Catalog 805)) := by
  let l : CertBound := ⟨true,true,⟨⟨(300531/169850),0,0,(50203/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1717407/1720561),(1283338/1720561),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3675015913529120313007826 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid805 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 805) (section14Witness section14Catalog 806)) := by
  let l : CertBound := ⟨true,true,⟨⟨(300531/169850),0,0,(50203/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-33504573/50976119),(29141215/50976119),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3624554100796690752439268 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid806 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 806) (section14Witness section14Catalog 807)) := by
  let l : CertBound := ⟨true,true,⟨⟨(789/430),0,0,(61/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2865827841497342118091177 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid807 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 807) (section14Witness section14Catalog 808)) := by
  let l : CertBound := ⟨true,true,⟨⟨(789/430),0,0,(61/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(352019471/339430907),(-129396314/339430907),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2737944949892778856239388 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid808 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 808) (section14Witness section14Catalog 809)) := by
  let l : CertBound := ⟨true,true,⟨⟨(789/430),0,0,(61/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-15117054/32393821),(15070079/32393821),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2786819394427883556392443 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid809 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 809) (section14Witness section14Catalog 810)) := by
  let l : CertBound := ⟨true,true,⟨⟨(789/430),0,0,(61/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-120696486/959751659),(279283134/959751659),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2736289881918647601214669 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid810 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 810) (section14Witness section14Catalog 811)) := by
  let l : CertBound := ⟨true,true,⟨⟨(862/6539),(2445/6539),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(357775/262078),0,0,(-1255075/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (596716197231266652928693 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid811 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 811) (section14Witness section14Catalog 812)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-3128689/24717923),(11441678/24717923),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(263/422),0,0,(-61/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (354850972732246711773796 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid812 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 812) (section14Witness section14Catalog 813)) := by
  let l : CertBound := ⟨true,true,⟨⟨(862/6539),(2445/6539),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7109/12685),0,0,(-224/12685)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (388352814253521048412920 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid813 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 813) (section14Witness section14Catalog 814)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9928/60671),(57548/182013),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7109/12685),0,0,(-224/12685)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (299688600961995379166011 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid814 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 814) (section14Witness section14Catalog 815)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(7109/12685),0,0,(-224/12685)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (672884646403340500265464 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid815 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 815) (section14Witness section14Catalog 816)) := by
  let l : CertBound := ⟨true,true,⟨⟨(862/6539),(2445/6539),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (103991924536562264360195 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid816 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 816) (section14Witness section14Catalog 817)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9928/60671),(57548/182013),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(701239/262078),0,0,(-351421/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (109072737767977714969885 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid817 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 817) (section14Witness section14Catalog 818)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (398593718193860252370325 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid818 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 818) (section14Witness section14Catalog 819)) := by
  let l : CertBound := ⟨true,false,⟨⟨(26413/47558),0,0,(19107/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(357775/262078),0,0,(-1255075/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (648046163055376026952022 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid819 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 819) (section14Witness section14Catalog 820)) := by
  let l : CertBound := ⟨true,false,⟨⟨(26413/47558),0,0,(19107/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(263/422),0,0,(-61/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (541728103178239925175685 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid820 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 820) (section14Witness section14Catalog 821)) := by
  let l : CertBound := ⟨true,false,⟨⟨(26413/47558),0,0,(19107/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (157967046061310377803009 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid821 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 821) (section14Witness section14Catalog 822)) := by
  let l : CertBound := ⟨true,false,⟨⟨(26413/47558),0,0,(19107/332906)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(701239/262078),0,0,(-351421/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (248754095390224639991694 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid822 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 822) (section14Witness section14Catalog 823)) := by
  let l : CertBound := ⟨true,true,⟨⟨(184891/169850),0,0,(19107/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(357775/262078),0,0,(-1255075/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1669462547253688399786293 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid823 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 823) (section14Witness section14Catalog 824)) := by
  let l : CertBound := ⟨true,true,⟨⟨(184891/169850),0,0,(19107/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(263/422),0,0,(-61/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1563410992101612473174603 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid824 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 824) (section14Witness section14Catalog 825)) := by
  let l : CertBound := ⟨true,true,⟨⟨(184891/169850),0,0,(19107/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1246185435383985122092870 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid825 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 825) (section14Witness section14Catalog 826)) := by
  let l : CertBound := ⟨true,true,⟨⟨(184891/169850),0,0,(19107/169850)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(701239/262078),0,0,(-351421/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1270170479588537012825964 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid826 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 826) (section14Witness section14Catalog 827)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32927/25370),0,0,(-297/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(357775/262078),0,0,(-1255075/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1202763471730376292611912 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid827 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 827) (section14Witness section14Catalog 828)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32927/25370),0,0,(-297/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(263/422),0,0,(-61/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1096659966785492417390084 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid828 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 828) (section14Witness section14Catalog 829)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32927/25370),0,0,(-297/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (760839723956453597475610 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid829 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 829) (section14Witness section14Catalog 830)) := by
  let l : CertBound := ⟨true,true,⟨⟨(32927/25370),0,0,(-297/25370)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(701239/262078),0,0,(-351421/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(213/790),0,0,(1/5530)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (803733205733539210606385 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid830 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 830) (section14Witness section14Catalog 831)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(17472/11581),(-8957/11581),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (573415159906457174971357 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid831 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 831) (section14Witness section14Catalog 832)) := by
  let l : CertBound := ⟨true,false,⟨⟨(1884725/3903158),0,0,(15295/557594)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(127151/150866),(-58285/150866),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (573858940723891481242380 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 768).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 768).take 64 = [⟨768,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],769⟩,⟨769,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],770⟩,⟨770,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],771⟩,⟨771,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],772⟩,⟨772,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],773⟩,⟨773,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],774⟩,⟨774,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],775⟩,⟨775,[1,2,3,5,6,7,10,11,13,14,15],776⟩,⟨776,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],777⟩,⟨777,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],778⟩,⟨778,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],779⟩,⟨779,[1,2,3,5,6,7,10,11,13,14,15],780⟩,⟨780,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],781⟩,⟨781,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],782⟩,⟨782,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],783⟩,⟨783,[1,2,3,5,6,7,10,11,13,14,15],784⟩,⟨784,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],785⟩,⟨785,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],786⟩,⟨786,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],787⟩,⟨787,[1,2,3,5,6,7,10,11,13,14,15],788⟩,⟨788,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],789⟩,⟨789,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],790⟩,⟨790,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],791⟩,⟨791,[1,4,5,6,7,8,9,10,11,12,13,16],792⟩,⟨792,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],793⟩,⟨793,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],794⟩,⟨794,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],795⟩,⟨795,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],796⟩,⟨796,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],797⟩,⟨797,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],798⟩,⟨798,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],799⟩,⟨799,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],800⟩,⟨800,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],801⟩,⟨801,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],802⟩,⟨802,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],803⟩,⟨803,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],804⟩,⟨804,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],805⟩,⟨805,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],806⟩,⟨806,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],807⟩,⟨807,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],808⟩,⟨808,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],809⟩,⟨809,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],810⟩,⟨810,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],811⟩,⟨811,[1,2,3,4,5,6,7,8,9,10,11,13,14,15,16],812⟩,⟨812,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],813⟩,⟨813,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],814⟩,⟨814,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],815⟩,⟨815,[1,4,5,6,8,9,10,12,13,16],816⟩,⟨816,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],817⟩,⟨817,[1,2,3,6,7,10,11,13,14,15],818⟩,⟨818,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],819⟩,⟨819,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],820⟩,⟨820,[1,4,5,8,9,10,12,13,16],821⟩,⟨821,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],822⟩,⟨822,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],823⟩,⟨823,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],824⟩,⟨824,[1,2,3,5,6,7,10,11,13,14,15],825⟩,⟨825,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],826⟩,⟨826,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],827⟩,⟨827,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],828⟩,⟨828,[1,2,3,5,6,7,10,11,13,14,15],829⟩,⟨829,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],830⟩,⟨830,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],831⟩,⟨831,[1,2,3,4,5,6,7,10,11,13,14,15,16],832⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid768
  · exact valid769
  · exact valid770
  · exact valid771
  · exact valid772
  · exact valid773
  · exact valid774
  · exact valid775
  · exact valid776
  · exact valid777
  · exact valid778
  · exact valid779
  · exact valid780
  · exact valid781
  · exact valid782
  · exact valid783
  · exact valid784
  · exact valid785
  · exact valid786
  · exact valid787
  · exact valid788
  · exact valid789
  · exact valid790
  · exact valid791
  · exact valid792
  · exact valid793
  · exact valid794
  · exact valid795
  · exact valid796
  · exact valid797
  · exact valid798
  · exact valid799
  · exact valid800
  · exact valid801
  · exact valid802
  · exact valid803
  · exact valid804
  · exact valid805
  · exact valid806
  · exact valid807
  · exact valid808
  · exact valid809
  · exact valid810
  · exact valid811
  · exact valid812
  · exact valid813
  · exact valid814
  · exact valid815
  · exact valid816
  · exact valid817
  · exact valid818
  · exact valid819
  · exact valid820
  · exact valid821
  · exact valid822
  · exact valid823
  · exact valid824
  · exact valid825
  · exact valid826
  · exact valid827
  · exact valid828
  · exact valid829
  · exact valid830
  · exact valid831
end Section14Numerical_768_832

#print axioms solution
