-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_0576_0640
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:25:25.359764+00:00
-- url     : https://prove2.me/submissions/166473d1-6bac-4f5d-8311-b0502df4d254

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_576_640
private theorem valid576 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 576) (section14Witness section14Catalog 577)) := by
  let l : CertBound := ⟨true,true,⟨⟨(8457/7802),0,0,(931/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1884725/3903158),0,0,(15295/557594)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1353277879762542004620448 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid577 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 577) (section14Witness section14Catalog 578)) := by
  let l : CertBound := ⟨true,true,⟨⟨(8457/7802),0,0,(931/7802)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1309971806107625316840743 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid578 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 578) (section14Witness section14Catalog 579)) := by
  let l : CertBound := ⟨true,true,⟨⟨(950149/771602),(703311/771602),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(739135/1834546),0,0,(-108575/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (3285019692910367336460887 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid579 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 579) (section14Witness section14Catalog 580)) := by
  let l : CertBound := ⟨true,true,⟨⟨(4725150/4659289),(11906131/13977867),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2523/5074),0,0,(-77/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2714005225079044215499489 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid580 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 580) (section14Witness section14Catalog 581)) := by
  let l : CertBound := ⟨true,true,⟨⟨(950149/771602),(703311/771602),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2921602053183343762906513 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid581 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 581) (section14Witness section14Catalog 582)) := by
  let l : CertBound := ⟨true,true,⟨⟨(4494823/3579589),(3096264/3579589),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1034789/1310390),0,0,(-30401/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2815498338867239121936199 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid582 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 582) (section14Witness section14Catalog 583)) := by
  let l : CertBound := ⟨true,true,⟨⟨(4064450/4659289),(4170517/4659289),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(739135/1834546),0,0,(-108575/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2775846910722469098021447 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid583 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 583) (section14Witness section14Catalog 584)) := by
  let l : CertBound := ⟨true,true,⟨⟨(8307659/19052634),(19189483/19052634),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2523/5074),0,0,(-77/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2307857121558725344971667 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid584 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 584) (section14Witness section14Catalog 585)) := by
  let l : CertBound := ⟨true,true,⟨⟨(4064450/4659289),(4170517/4659289),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2391734304019591705083314 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid585 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 585) (section14Witness section14Catalog 586)) := by
  let l : CertBound := ⟨true,true,⟨⟨(3160489/3325417),(2733515/3325417),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1034789/1310390),0,0,(-30401/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2316524098086476929691278 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid586 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 586) (section14Witness section14Catalog 587)) := by
  let l : CertBound := ⟨true,true,⟨⟨(50142285/35951422),(23544709/35951422),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(739135/1834546),0,0,(-108575/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2915340028248604564517689 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid587 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 587) (section14Witness section14Catalog 588)) := by
  let l : CertBound := ⟨true,true,⟨⟨(280718947/217091279),(118739022/217091279),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2523/5074),0,0,(-77/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2386392805649617631703310 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid588 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 588) (section14Witness section14Catalog 589)) := by
  let l : CertBound := ⟨true,true,⟨⟨(50142285/35951422),(23544709/35951422),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2537051572010528747871970 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid589 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 589) (section14Witness section14Catalog 590)) := by
  let l : CertBound := ⟨true,true,⟨⟨(236668450/166784579),(101469470/166784579),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1034789/1310390),0,0,(-30401/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2445941670244186572725499 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid590 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 590) (section14Witness section14Catalog 591)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-5827030/5460911),(12492497/16382733),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (610367589428837648770290 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid591 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 591) (section14Witness section14Catalog 592)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7199737/6882244),(-7612151/17205610),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (573954207356712861468971 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid592 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 592) (section14Witness section14Catalog 593)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-748551/1448101),(2031182/4344303),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (555852737512260770289784 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid593 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 593) (section14Witness section14Catalog 594)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(24122/44759),(-22358/134277),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (598422925982109869914287 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid594 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 594) (section14Witness section14Catalog 595)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(41389278/95068429),(-9869146/95068429),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(113/179),(1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (740881897247685588118487 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid595 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 595) (section14Witness section14Catalog 596)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(24122/44759),(-22358/134277),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1821241261991223110387284 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid596 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 596) (section14Witness section14Catalog 597)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(9045083/24035583),(-1472729/24035583),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1134011419890707550332371 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid597 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 597) (section14Witness section14Catalog 598)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1295924/2569417),(-375018/2569417),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (596678352106844651372593 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid598 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 598) (section14Witness section14Catalog 599)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(185094441/444860953),(-40951204/444860953),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(113/179),(1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (739170069154084591742756 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid599 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 599) (section14Witness section14Catalog 600)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1295924/2569417),(-375018/2569417),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1819591317288451669946055 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid600 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 600) (section14Witness section14Catalog 601)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(163926387/459925643),(-67803152/1379776929),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(731/2497),(-1/2497),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1132199305389605976565818 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid601 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 601) (section14Witness section14Catalog 602)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(6155/11869),(-1825/11869),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (595653012466172382965211 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid602 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 602) (section14Witness section14Catalog 603)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(10599915/25209839),(-2374695/25209839),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(113/179),(1/537),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (738131004098921418145259 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid603 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 603) (section14Witness section14Catalog 604)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(6155/11869),(-1825/11869),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1818385770651054095881626 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid604 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 604) (section14Witness section14Catalog 605)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(2268814/6373653),(-309302/6373653),0,0⟩,⟨(1590/5893),(1/5893),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(22/37),(1/37),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1131201180438814336306546 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid605 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 605) (section14Witness section14Catalog 606)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(739135/1834546),0,0,(-108575/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (526755628606349632718044 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid606 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 606) (section14Witness section14Catalog 607)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2523/5074),0,0,(-77/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (368869106493004740287071 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid607 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 607) (section14Witness section14Catalog 608)) := by
  let l : CertBound := ⟨true,true,⟨⟨(189609/785686),(191283/785686),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1658989043212721482242 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid608 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 608) (section14Witness section14Catalog 609)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1034789/1310390),0,0,(-30401/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (110639154835758611907589 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid609 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 609) (section14Witness section14Catalog 610)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(739135/1834546),0,0,(-108575/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (613802778856593461711567 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid610 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 610) (section14Witness section14Catalog 611)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2523/5074),0,0,(-77/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (451835911292622169532102 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid611 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 611) (section14Witness section14Catalog 612)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (48907867361783510769462 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid612 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 612) (section14Witness section14Catalog 613)) := by
  let l : CertBound := ⟨true,false,⟨⟨(5/7),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1034789/1310390),0,0,(-30401/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (81104832917378996418911 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid613 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 613) (section14Witness section14Catalog 614)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(739135/1834546),0,0,(-108575/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1629276735918280697303540 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid614 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 614) (section14Witness section14Catalog 615)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2523/5074),0,0,(-77/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1468014077311602698006851 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid615 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 615) (section14Witness section14Catalog 616)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1159855361056602807141950 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid616 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 616) (section14Witness section14Catalog 617)) := by
  let l : CertBound := ⟨true,true,⟨⟨(7/5),0,0,0⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1034789/1310390),0,0,(-30401/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1203053446558923184954672 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid617 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 617) (section14Witness section14Catalog 618)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(739135/1834546),0,0,(-108575/5503638)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1068885764803708130857128 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid618 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 618) (section14Witness section14Catalog 619)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2523/5074),0,0,(-77/5074)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (909993282256951457688226 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid619 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 619) (section14Witness section14Catalog 620)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (585787418381571107822279 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid620 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 620) (section14Witness section14Catalog 621)) := by
  let l : CertBound := ⟨true,true,⟨⟨1,0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1034789/1310390),0,0,(-30401/786234)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (649903342225575156406819 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid621 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 621) (section14Witness section14Catalog 622)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(11/210)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (767907505190969530864934 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid622 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 622) (section14Witness section14Catalog 623)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/17),0,0,(4/51)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (653205481370870987531460 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid623 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 623) (section14Witness section14Catalog 624)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-54/407),(85/407),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (595489571792301094549775 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid624 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 624) (section14Witness section14Catalog 625)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1455/5291),(3191/10582),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (562071357866523217314199 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid625 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 625) (section14Witness section14Catalog 626)) := by
  let l : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (964743451964010056774730 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid626 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 626) (section14Witness section14Catalog 627)) := by
  let l : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1/10),0,0,(11/210)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (899256758563092629302385 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid627 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 627) (section14Witness section14Catalog 628)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1/5291),(809/5291),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (531725479655229208339132 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid628 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 628) (section14Witness section14Catalog 629)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-63/50),0,0,(23/50)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (110666297666465259579437 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid629 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 629) (section14Witness section14Catalog 630)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(343/5050),0,0,(413/5050)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (55423714817103898050931 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid630 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 630) (section14Witness section14Catalog 631)) := by
  let l : CertBound := ⟨true,true,⟨⟨(-145/4189),(5312/12567),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(12/47),(1/47),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(2541/5050),0,0,(-259/5050)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (638421660672116598744429 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid631 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 631) (section14Witness section14Catalog 632)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(363/1414),0,0,(-37/1414)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (682063936778866653157319 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid632 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 632) (section14Witness section14Catalog 633)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-1/34),0,0,(19/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (728522974248214980301542 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid633 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 633) (section14Witness section14Catalog 634)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-3/10),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (612639214693344028081200 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid634 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 634) (section14Witness section14Catalog 635)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(7/202),0,0,(59/1414)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (558373209997082376229825 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid635 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 635) (section14Witness section14Catalog 636)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-9/14),0,0,(23/98)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let R : CertRectangle := ⟨(1/3),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (485335147768187251142666 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid636 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 636) (section14Witness section14Catalog 637)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-49/850),0,0,(133/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (557789031387457556642500 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid637 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 637) (section14Witness section14Catalog 638)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(9/10),0,0,(-1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (283991977824291405554162 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid638 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 638) (section14Witness section14Catalog 639)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(35255/336938),0,0,(1145/336938)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (682278150478978007806058 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid639 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 639) (section14Witness section14Catalog 640)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(265/1394),0,0,(-5/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (609518681262366958188628 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 576).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 576).take 64 = [⟨576,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],577⟩,⟨577,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],578⟩,⟨578,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],579⟩,⟨579,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],580⟩,⟨580,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],581⟩,⟨581,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],582⟩,⟨582,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],583⟩,⟨583,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],584⟩,⟨584,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],585⟩,⟨585,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],586⟩,⟨586,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],587⟩,⟨587,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],588⟩,⟨588,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],589⟩,⟨589,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],590⟩,⟨590,[1,4,5,6,8,9,10,12,13,16],591⟩,⟨591,[1,4,5,6,8,9,10,12,13,16],592⟩,⟨592,[1,4,5,6,8,9,10,12,13,16],593⟩,⟨593,[1,4,5,6,8,9,10,12,13,16],594⟩,⟨594,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],595⟩,⟨595,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],596⟩,⟨596,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],597⟩,⟨597,[1,4,5,6,8,9,10,12,13,16],598⟩,⟨598,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],599⟩,⟨599,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],600⟩,⟨600,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],601⟩,⟨601,[1,4,5,6,8,9,10,12,13,16],602⟩,⟨602,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],603⟩,⟨603,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],604⟩,⟨604,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],605⟩,⟨605,[1,5,6,10,13],606⟩,⟨606,[1,5,6,10,13],607⟩,⟨607,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],608⟩,⟨608,[1,5,6,10,13],609⟩,⟨609,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],610⟩,⟨610,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],611⟩,⟨611,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],612⟩,⟨612,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],613⟩,⟨613,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],614⟩,⟨614,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],615⟩,⟨615,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],616⟩,⟨616,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],617⟩,⟨617,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],618⟩,⟨618,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],619⟩,⟨619,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],620⟩,⟨620,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],621⟩,⟨621,[1,4,5,6,8,9,10,12,13,16],622⟩,⟨622,[1,4,5,6,8,9,10,12],623⟩,⟨623,[1,4,5,6,8,9,10,12],624⟩,⟨624,[1,4,5,6,8,9,10,12],625⟩,⟨625,[1,2,4,5,6,8,9,10,12],626⟩,⟨626,[1,2,4,5,6,8,9,10,12],627⟩,⟨627,[1,5,6,9,10],628⟩,⟨628,[1,2,3,5,6,7,13,14,15],629⟩,⟨629,[1,2,4,5,6,8,9,10,12,13,14,16],630⟩,⟨630,[1,2,3,5,6,7,9,10,11,13,14,15],631⟩,⟨631,[1,2,3,5,6,7,9,10,11,13,14,15],632⟩,⟨632,[1,2,4,5,6,8,9,10,12,13,14,16],633⟩,⟨633,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],634⟩,⟨634,[1,2,4,5,6,8,9,10,12,13,14,16],635⟩,⟨635,[1,2,3,5,6,7,13,14,15],636⟩,⟨636,[1,2,4,5,6,8,9,10,12,13,14,16],637⟩,⟨637,[1,2,3,4,5,6,7,8,9,10,12,13,14,15,16],638⟩,⟨638,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],639⟩,⟨639,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],640⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid576
  · exact valid577
  · exact valid578
  · exact valid579
  · exact valid580
  · exact valid581
  · exact valid582
  · exact valid583
  · exact valid584
  · exact valid585
  · exact valid586
  · exact valid587
  · exact valid588
  · exact valid589
  · exact valid590
  · exact valid591
  · exact valid592
  · exact valid593
  · exact valid594
  · exact valid595
  · exact valid596
  · exact valid597
  · exact valid598
  · exact valid599
  · exact valid600
  · exact valid601
  · exact valid602
  · exact valid603
  · exact valid604
  · exact valid605
  · exact valid606
  · exact valid607
  · exact valid608
  · exact valid609
  · exact valid610
  · exact valid611
  · exact valid612
  · exact valid613
  · exact valid614
  · exact valid615
  · exact valid616
  · exact valid617
  · exact valid618
  · exact valid619
  · exact valid620
  · exact valid621
  · exact valid622
  · exact valid623
  · exact valid624
  · exact valid625
  · exact valid626
  · exact valid627
  · exact valid628
  · exact valid629
  · exact valid630
  · exact valid631
  · exact valid632
  · exact valid633
  · exact valid634
  · exact valid635
  · exact valid636
  · exact valid637
  · exact valid638
  · exact valid639
end Section14Numerical_576_640

#print axioms solution
