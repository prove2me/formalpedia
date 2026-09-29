-- Prove2me | solution 1 for Freiman.section14_pairWitnesses_0704_0768
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T10:25:53.124617+00:00
-- url     : https://prove2.me/submissions/4be73dde-9ac2-4034-af6d-9ffc05f5b4df

import Definitions.Def_Freiman_section14Data

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace Section14Numerical_704_768
private theorem valid704 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 704) (section14Witness section14Catalog 705)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(3461375/53222218),0,0,(-28125/7603174)⟩,⟨(9683/36034),0,0,(1/36034)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (740154561600063840920297 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid705 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 705) (section14Witness section14Catalog 706)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(4543/70474),0,0,(-9/493318)⟩,⟨(89/334),0,0,(1/2338)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (717218233361200557665234 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid706 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 706) (section14Witness section14Catalog 707)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(83859/1143410),0,0,(-131/1143410)⟩,⟨(561/2098),0,0,(1/2098)⟩,⟨(299/1090),0,0,(-1/1090)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (705885747904975334714679 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid707 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 707) (section14Witness section14Catalog 708)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-485017/17514937),(1272635/17514937),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (670264563335910241295662 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid708 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 708) (section14Witness section14Catalog 709)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-2144113/41398942),(11411453/124196826),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(175/647),(-1/1941),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (657447329609435896576708 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid709 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 709) (section14Witness section14Catalog 710)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(5016954/464511289),(27364771/464511289),0,0⟩,⟨(660/2461),(1/2461),0,0⟩,⟨(9257/34318),(-1/34318),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (649787180341102594366139 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid710 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 710) (section14Witness section14Catalog 711)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(969185/7603174),0,0,(-55125/7603174)⟩,⟨(9683/36034),0,0,(1/36034)⟩,⟨(115/422),0,0,(-1/1266)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (675790748023787264316669 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid711 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 711) (section14Witness section14Catalog 712)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1305/9478),0,0,(-1255/199038)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (682273276586862649572901 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid712 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 712) (section14Witness section14Catalog 713)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9093/24067),0,0,(1036/24067)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1305/9478),0,0,(-1255/199038)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (760178124076422152152313 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid713 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 713) (section14Witness section14Catalog 714)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(15/94),0,0,(-5/1974)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (614514258824243515852644 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid714 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 714) (section14Witness section14Catalog 715)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9093/24067),0,0,(1036/24067)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(15/94),0,0,(-5/1974)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (692006296467692025602448 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid715 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 715) (section14Witness section14Catalog 716)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(265/1394),0,0,(-5/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (585845967346418663982766 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid716 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 716) (section14Witness section14Catalog 717)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1805/23782),(12589/71346),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (489510163046596935875620 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid717 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 717) (section14Witness section14Catalog 718)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-8035/56212),(3194/14053),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(113/179),(1/537),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (456453254063919851608932 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid718 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 718) (section14Witness section14Catalog 719)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9093/24067),0,0,(1036/24067)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1805/23782),(12589/71346),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (567128695991902430220036 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid719 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 719) (section14Witness section14Catalog 720)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(28051/1291466),(181029/1291466),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(22/37),(1/37),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (434325042849814431539284 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid720 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 720) (section14Witness section14Catalog 721)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1827/6770),0,0,(-251/20310)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (517642005514261615073517 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid721 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 721) (section14Witness section14Catalog 722)) := by
  let l : CertBound := ⟨true,true,⟨⟨(9093/24067),0,0,(1036/24067)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(107/170),0,0,(1/510)⟩,⟨(11/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1827/6770),0,0,(-251/20310)⟩,⟨(523/1354),0,0,(1/1354)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(1/10),0,0,(1/10)⟩,⟨(119/202),0,0,(-1/202)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (595009202074918790299061 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid722 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 722) (section14Witness section14Catalog 723)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(445/48134),0,0,(2115/336938)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (854349840153482047291999 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid723 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 723) (section14Witness section14Catalog 724)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-37/1394),0,0,(27/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (817166095940270417281805 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid724 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 724) (section14Witness section14Catalog 725)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-536/11891),(875/11891),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (773651203897127609363189 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid725 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 725) (section14Witness section14Catalog 726)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(4361/240670),0,0,(2961/240670)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (784216717647340558853764 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid726 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 726) (section14Witness section14Catalog 727)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1330/14053),(2979/28106),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (760965971849792276669186 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid727 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 727) (section14Witness section14Catalog 728)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-4897/361537),(22359/361537),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (752786519847758278310297 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid728 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 728) (section14Witness section14Catalog 729)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1/235),0,0,(16/4935)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (841161329978570552913990 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid729 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 729) (section14Witness section14Catalog 730)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-11/1025),0,0,(28/3075)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(1/10),0,0,(1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (822936750349632664807505 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid730 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 730) (section14Witness section14Catalog 731)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-1043/46079),(1720/46079),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (799530787665404856473788 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid731 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 731) (section14Witness section14Catalog 732)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(49/5875),0,0,(112/17625)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(7/10),0,0,(1/70)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (805896404863776860484310 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid732 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 732) (section14Witness section14Catalog 733)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-5195/108914),(2926/54457),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (793060500931389932434358 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid733 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 733) (section14Witness section14Catalog 734)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(-12696/2146969),(66601/2146969),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(1/2),(1/6),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (788731304826893546728747 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid734 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 734) (section14Witness section14Catalog 735)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/3),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (494772009702009165579037 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid735 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 735) (section14Witness section14Catalog 736)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(117/238),0,0,(-31/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (405591650521375092383950 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid736 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 736) (section14Witness section14Catalog 737)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1282125/1662878),0,0,(-168625/1662878)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (390990792402192027658400 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid737 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 737) (section14Witness section14Catalog 738)) := by
  let l : CertBound := ⟨true,true,⟨⟨(819/850),0,0,(-217/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1282125/1662878),0,0,(-168625/1662878)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (396103489047576267329908 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid738 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 738) (section14Witness section14Catalog 739)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1/2),0,0,(-1/42)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (274614152834760352724919 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid739 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 739) (section14Witness section14Catalog 740)) := by
  let l : CertBound := ⟨true,true,⟨⟨(819/850),0,0,(-217/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(291/514),0,0,(-19/514)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (271168062943110554444422 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid740 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 740) (section14Witness section14Catalog 741)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(291/514),0,0,(-19/514)⟩,⟨(147/514),0,0,(1/514)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (263579849381503422230648 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid741 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 741) (section14Witness section14Catalog 742)) := by
  let l : CertBound := ⟨true,true,⟨⟨(358995/237554),0,0,(-47215/237554)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(117/238),0,0,(-31/714)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (405076450307704589336716 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid742 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 742) (section14Witness section14Catalog 743)) := by
  let l : CertBound := ⟨true,true,⟨⟨(358995/237554),0,0,(-47215/237554)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1/2),0,0,(-1/42)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (280421214821031893496882 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid743 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 743) (section14Witness section14Catalog 744)) := by
  let l : CertBound := ⟨true,true,⟨⟨(358995/237554),0,0,(-47215/237554)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-77549/206349),(31001/68783),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (252358367896925410318847 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid744 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 744) (section14Witness section14Catalog 745)) := by
  let l : CertBound := ⟨true,true,⟨⟨(358995/237554),0,0,(-47215/237554)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(689/2350),0,0,(-1/2350)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-67190/998283),(99522/332761),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (190563592879177603165128 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid745 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 745) (section14Witness section14Catalog 746)) := by
  let l : CertBound := ⟨true,true,⟨⟨(819/850),0,0,(-217/2550)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-511868/1465607),(641519/1465607),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (247842003253788424051658 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid746 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 746) (section14Witness section14Catalog 747)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-66667/1636239),(156036/545413),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (174705288159029287564557 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid747 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 747) (section14Witness section14Catalog 748)) := by
  let l : CertBound := ⟨true,true,⟨⟨(290431/478478),(129331/478478),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1044983750789402133556709 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid748 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 748) (section14Witness section14Catalog 749)) := by
  let l : CertBound := ⟨true,true,⟨⟨(11675299/19275828),(4527065/19275828),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(221/514),0,0,(-5/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (825321145530009679987000 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid749 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 749) (section14Witness section14Catalog 750)) := by
  let l : CertBound := ⟨true,true,⟨⟨(290431/478478),(129331/478478),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(225555/118777),0,0,(-238400/831439)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (651540039320144784486000 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid750 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 750) (section14Witness section14Catalog 751)) := by
  let l : CertBound := ⟨true,true,⟨⟨(658540/1012583),(1639266/7088081),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1856617/2787970),0,0,(-14189/557594)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (659228002512402963068449 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid751 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 751) (section14Witness section14Catalog 752)) := by
  let l : CertBound := ⟨true,true,⟨⟨(134765/220597),(599154/2426567),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (997133513213782491000433 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid752 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 752) (section14Witness section14Catalog 753)) := by
  let l : CertBound := ⟨true,true,⟨⟨(169686252/264154033),(154462523/792462099),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(221/514),0,0,(-5/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (782807081429247842315088 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid753 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 753) (section14Witness section14Catalog 754)) := by
  let l : CertBound := ⟨true,true,⟨⟨(134765/220597),(599154/2426567),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (485827360200739942448835 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid754 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 754) (section14Witness section14Catalog 755)) := by
  let l : CertBound := ⟨true,true,⟨⟨(48344198/71893393),(14226022/71893393),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(1413/4654),(-1/4654),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1856617/2787970),0,0,(-14189/557594)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (612456017386763066719856 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid755 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 755) (section14Witness section14Catalog 756)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2210439/593885),0,0,(-66752/118777)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1144636991031529138624336 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid756 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 756) (section14Witness section14Catalog 757)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2210439/593885),0,0,(-66752/118777)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(221/514),0,0,(-5/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1007150186072050358194746 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid757 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 757) (section14Witness section14Catalog 758)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2210439/593885),0,0,(-66752/118777)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (635886745547511372588578 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid758 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 758) (section14Witness section14Catalog 759)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2210439/593885),0,0,(-66752/118777)⟩,⟨(1719/5794),0,0,(1/5794)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(189/622),0,0,(-1/4354)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1856617/2787970),0,0,(-14189/557594)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (788927449877876524341716 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid759 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 759) (section14Witness section14Catalog 760)) := by
  let l : CertBound := ⟨true,true,⟨⟨(476376/728233),(1155575/5097631),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1007740760718982219570195 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid760 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 760) (section14Witness section14Catalog 761)) := by
  let l : CertBound := ⟨true,true,⟨⟨(46565227/68453902),(18112387/102680853),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(221/514),0,0,(-5/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (790264406022072745097268 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid761 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 761) (section14Witness section14Catalog 762)) := by
  let l : CertBound := ⟨true,true,⟨⟨(476376/728233),(1155575/5097631),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(-2334/781),(1646/781),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨2,-1,0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (496907435664851305911266 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid762 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 762) (section14Witness section14Catalog 763)) := by
  let l : CertBound := ⟨true,true,⟨⟨(210693975/302061298),(8097951/43151614),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(71/229),(-1/229),0,0⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1856617/2787970),0,0,(-14189/557594)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (622035254027072202581848 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid763 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 763) (section14Witness section14Catalog 764)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2497/2050),0,0,(273/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(1326155/3903158),0,0,(-50675/3903158)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2048060398303422994733903 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid764 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 764) (section14Witness section14Catalog 765)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2497/2050),0,0,(273/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(221/514),0,0,(-5/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(147/514),0,0,(-1/514)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1911267517832166399531209 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid765 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 765) (section14Witness section14Catalog 766)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2497/2050),0,0,(273/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,false,⟨⟨(1856617/2787970),0,0,(-14189/557594)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (1692924186997558321842033 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid766 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 766) (section14Witness section14Catalog 767)) := by
  let l : CertBound := ⟨true,false,⟨⟨(279/500),0,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(125/214),(-1/214),0,0⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(20605417/16123461),(-9037402/16123461),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (385479992383213777075805 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
private theorem valid767 : certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog 767) (section14Witness section14Catalog 768)) := by
  let l : CertBound := ⟨true,true,⟨⟨(2497/2050),0,0,(273/2050)⟩,⟨(13/50),0,0,(1/150)⟩,⟨(29/82),0,0,(-1/82)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩
  let u : CertBound := ⟨false,true,⟨⟨(20605417/16123461),(-9037402/16123461),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩,⟨(133/478),(-1/478),0,0⟩,⟨(3289/10753),(1/10753),0,0⟩⟩⟩
  let R : CertRectangle := ⟨(1/4),(4/5),(1/4),(4/5)⟩
  change certWitnessValid (⟨l,u,R,certBernsteinCoefficients (certCrossPolynomial l.threshold u.threshold) R, fun _ _ => (2023317146622907083071219 : ℚ)/(2*10^24)⟩ : CertWitness)
  unfold certWitnessValid
  refine ⟨rfl,rfl,?_,?_,?_,?_,rfl,?_,?_⟩
  all_goals simp only [certRectangleValid,certThresholdDataValid,certCoefficientBoundValid]
  all_goals decide +kernel
theorem _root_.solution : ∀ a ∈ (section14Catalog.assignments.drop 704).take 64, certWitnessValid (section14PairWitness section14Catalog (section14Proof section14Catalog a.proofId) (section14Witness section14Catalog a.witnessId)) := by
  have hs : (section14Catalog.assignments.drop 704).take 64 = [⟨704,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],705⟩,⟨705,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],706⟩,⟨706,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],707⟩,⟨707,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],708⟩,⟨708,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],709⟩,⟨709,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],710⟩,⟨710,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],711⟩,⟨711,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],712⟩,⟨712,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],713⟩,⟨713,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],714⟩,⟨714,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],715⟩,⟨715,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],716⟩,⟨716,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],717⟩,⟨717,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],718⟩,⟨718,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],719⟩,⟨719,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],720⟩,⟨720,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],721⟩,⟨721,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],722⟩,⟨722,[1,2,4,5,6,8,9,10,12,13,14,16],723⟩,⟨723,[1,2,4,5,6,8,9,10,12,13,14,16],724⟩,⟨724,[1,2,4,5,6,8,9,10,12,13,14,16],725⟩,⟨725,[1,2,4,5,6,8,9,10,12,13,14,16],726⟩,⟨726,[1,2,4,5,6,8,9,10,12,13,14,16],727⟩,⟨727,[1,2,4,5,6,8,9,10,12,13,14,16],728⟩,⟨728,[1,2,4,5,6,8,9,10,12],729⟩,⟨729,[1,2,4,5,6,8,9,10,12],730⟩,⟨730,[1,2,4,5,6,8,9,10,12],731⟩,⟨731,[1,2,4,5,6,8,9,10,12],732⟩,⟨732,[1,2,4,5,6,8,9,10,12],733⟩,⟨733,[1,2,4,5,6,8,9,10,12],734⟩,⟨734,[1,2,5,6,9,10,13,14],735⟩,⟨735,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],736⟩,⟨736,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],737⟩,⟨737,[1,2,3,4,5,6,7,10,11,13,14,15,16],738⟩,⟨738,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],739⟩,⟨739,[1,2,3,4,5,6,7,10,11,13,14,15,16],740⟩,⟨740,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],741⟩,⟨741,[1,2,3,6,7,10,11,13,14,15],742⟩,⟨742,[1,2,3,6,7,10,11,13,14,15],743⟩,⟨743,[1,2,3,6,7,11,13,14,15],744⟩,⟨744,[1,2,3,6,7,10,11,13,14,15],745⟩,⟨745,[1,2,3,4,5,6,7,10,11,13,14,15,16],746⟩,⟨746,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],747⟩,⟨747,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],748⟩,⟨748,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],749⟩,⟨749,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],750⟩,⟨750,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],751⟩,⟨751,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],752⟩,⟨752,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],753⟩,⟨753,[1,2,3,5,6,7,10,11,13,14,15],754⟩,⟨754,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],755⟩,⟨755,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],756⟩,⟨756,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],757⟩,⟨757,[1,2,3,5,6,7,10,11,13,14,15],758⟩,⟨758,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],759⟩,⟨759,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],760⟩,⟨760,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],761⟩,⟨761,[1,2,3,5,6,7,10,11,13,14,15],762⟩,⟨762,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],763⟩,⟨763,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],764⟩,⟨764,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],765⟩,⟨765,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],766⟩,⟨766,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],767⟩,⟨767,[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16],768⟩] := by rfl
  rw [hs]
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact valid704
  · exact valid705
  · exact valid706
  · exact valid707
  · exact valid708
  · exact valid709
  · exact valid710
  · exact valid711
  · exact valid712
  · exact valid713
  · exact valid714
  · exact valid715
  · exact valid716
  · exact valid717
  · exact valid718
  · exact valid719
  · exact valid720
  · exact valid721
  · exact valid722
  · exact valid723
  · exact valid724
  · exact valid725
  · exact valid726
  · exact valid727
  · exact valid728
  · exact valid729
  · exact valid730
  · exact valid731
  · exact valid732
  · exact valid733
  · exact valid734
  · exact valid735
  · exact valid736
  · exact valid737
  · exact valid738
  · exact valid739
  · exact valid740
  · exact valid741
  · exact valid742
  · exact valid743
  · exact valid744
  · exact valid745
  · exact valid746
  · exact valid747
  · exact valid748
  · exact valid749
  · exact valid750
  · exact valid751
  · exact valid752
  · exact valid753
  · exact valid754
  · exact valid755
  · exact valid756
  · exact valid757
  · exact valid758
  · exact valid759
  · exact valid760
  · exact valid761
  · exact valid762
  · exact valid763
  · exact valid764
  · exact valid765
  · exact valid766
  · exact valid767
end Section14Numerical_704_768

#print axioms solution
