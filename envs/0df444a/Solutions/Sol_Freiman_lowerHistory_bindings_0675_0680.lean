-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0675_0680
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T01:32:30.275238+00:00
-- url     : https://prove2.me/submissions/d9d11509-5adc-4d95-8c86-f39f8b7ab816

import Definitions.Def_Freiman_lowerHistorySource
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Definitions.Def_Freiman_lowerHistoryVerification

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace M7SplitSep17
namespace RootInv18
theorem quadratic_three (a b : ℚ) :
    lowerHistoryInv ⟨a,b,0,0⟩ =
      ⟨a / (a^2 - 3*b^2), -b / (a^2 - 3*b^2), 0, 0⟩ := by
  have hd : (a^2 + 3*b^2)^2 - 3*(2*a*b)^2 = (a^2-3*b^2)^2 := by ring
  simp only [lowerHistoryInv, certFieldScale, certFieldMul]
  dsimp
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero, add_zero,
    neg_zero, zero_mul]
  rw [hd]
  by_cases h : a^2 - 3*b^2 = 0
  · simp [h]
  · congr 1 <;> field_simp <;> ring

theorem quadratic_twenty_one (a d : ℚ) :
    lowerHistoryInv ⟨a,0,0,d⟩ =
      ⟨a / (a^2 - 21*d^2), 0, 0, -d / (a^2 - 21*d^2)⟩ := by
  simp only [lowerHistoryInv, certFieldScale, certFieldMul]
  dsimp
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, sub_zero, add_zero,
    neg_zero, zero_mul]
  by_cases h : a^2 - 21*d^2 = 0
  · simp [h]
  · congr 1 <;> field_simp <;> ring
end RootInv18
namespace BindingNumeric20
def h2 : CertBound := ⟨true,true,⟨⟨37/50,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩,⟨125/214,-1/214,0,0⟩,⟨52/73,1/73,0,0⟩⟩⟩
def h5 : CertBound := ⟨false,true,⟨⟨279/500,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨66/179,-1/537,0,0⟩,⟨4/13,1/13,0,0⟩,⟨125/214,-1/214,0,0⟩⟩⟩
def h6 : CertBound := ⟨false,true,⟨⟨69/200,0,0,0⟩,⟨39/134,0,0,1/402⟩,⟨15/34,0,0,-1/34⟩,⟨1/10,0,0,1/10⟩,⟨119/202,0,0,-1/202⟩⟩⟩
def h7 : CertBound := ⟨true,false,⟨⟨31/100,0,0,0⟩,⟨5/22,1/22,0,0⟩,⟨2,-1,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
def h7m : CertBound := ⟨false,true,⟨⟨161/500,0,0,0⟩,⟨5/22,1/22,0,0⟩,⟨2,-1,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
def h9 : CertBound := ⟨false,false,⟨⟨3/2,-1/2,0,0⟩,⟨-1/2,1/2,0,0⟩,⟨4/13,1/13,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
def h21 : CertBound := ⟨false,true,⟨⟨-2334/781,1646/781,0,0⟩,⟨4/13,1/13,0,0⟩,⟨2,-1,0,0⟩,⟨42/143,1/429,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
def h23 : CertBound := ⟨true,true,⟨⟨139/250,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩,⟨1/2,1/6,0,0⟩,⟨125/214,-1/214,0,0⟩⟩⟩
def hn : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨-3/2,0,0,1/2⟩,⟨-1/2,0,0,1/6⟩,⟨-3/2,0,0,1/2⟩,⟨-1/2,0,0,1/6⟩⟩⟩
theorem bases : lowerHistoryH2=h2 ∧ lowerHistoryH5=h5 ∧ lowerHistoryH6=h6 ∧ lowerHistoryH7=h7 ∧ lowerHistoryH7Mixed=h7m ∧ lowerHistoryH9=h9 ∧ lowerHistoryH21=h21 ∧ lowerHistoryH23=h23 ∧ lowerHistoryHN=hn := by
  norm_num [h2,h5,h6,h7,h7m,h9,h21,h23,hn,lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7,lowerHistoryH7Mixed,lowerHistoryH9,lowerHistoryH21,lowerHistoryH23,lowerHistoryHN,lowerHistoryPB,lowerHistoryTheta,lowerHistoryConstantBound,lowerHistoryThreshold,lowerHistorySort,lowerHistoryLex,lowerHistoryWH,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryDiv,RootInv18.quadratic_three,RootInv18.quadratic_twenty_one,lowerHistoryAbs,lowerHistorySign,lowerHistoryQuadSign,lowerHistoryRatSign,lowerHistoryNeg,lowerHistoryAlpha,lowerHistoryBeta,lowerHistoryTau,lowerHistoryRat,certFieldScale,certFieldMul,certFieldAdd,certFieldSub]
theorem bh2 : lowerHistoryH2=h2 := bases.1
theorem bh5 : lowerHistoryH5=h5 := bases.2.1
theorem bh6 : lowerHistoryH6=h6 := bases.2.2.1
theorem bh7 : lowerHistoryH7=h7 := bases.2.2.2.1
theorem bh7m : lowerHistoryH7Mixed=h7m := bases.2.2.2.2.1
theorem bh9 : lowerHistoryH9=h9 := bases.2.2.2.2.2.1
theorem bh21 : lowerHistoryH21=h21 := bases.2.2.2.2.2.2.1
theorem bh23 : lowerHistoryH23=h23 := bases.2.2.2.2.2.2.2.1
theorem bhn : lowerHistoryHN=hn := bases.2.2.2.2.2.2.2.2
theorem initial_base : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
    [⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩,⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩,⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩,⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩] := by
  rw [bhn, bh7, bh9]
  rfl

end BindingNumeric20
end M7SplitSep17

open Freiman
namespace M7SplitSep17
namespace RootOps19
structure SourceOps where
  relaxed : LowerHistoryContext → Option (List CertBound)
  necessary : LowerHistoryState → LowerPair → Option (List CertBound)
  normalization : LowerPair → Bool → Bool → CertBound
  pull : CertBound → LowerPair → Bool → CertBound

def actualOps : SourceOps :=
  ⟨lowerHistoryRelaxedGoodness, lowerHistoryNecessary, lowerHistoryNormalization, lowerHistoryPull⟩

def eval (ops : SourceOps) (p : LowerHistoryPath) : List (List CertBound) := Id.run do
  let base : LowerPair := (p.context,if p.catalog = .initial then [3,1,3] else [3,1])
  let mut alternatives : List (List CertBound) := []
  if p.catalog = .initial then
    alternatives := [[lowerHistoryZero,lowerHistoryHN,
      lowerHistoryConstantBound (729/1024) true true,
      lowerHistoryConstantBound (225/289) false true]]
  else
    match ops.relaxed ⟨base,(false,false)⟩ with
    | none => return []
    | some good => alternatives := [[lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,
        lowerHistoryComplement lowerHistoryH9] ++ good]
  let mut words := lowerHistoryRawStep ([],[]) false p.entry
  let mut s := lowerHistoryInitialState p
  alternatives := alternatives.map fun cs => cs ++ [ops.normalization words s.wider false]
  for (l,reflect) in p.steps do
    match ops.necessary s words with
    | none => return []
    | some good =>
      alternatives := alternatives.flatMap fun cs =>
        (lowerHistorySourceChoices s l).map fun ch =>
          cs ++ good ++ ch.map (fun b => ops.pull b words s.wider)
    words := lowerHistoryRawStep words s.wider l
    s := lowerHistoryAdvance s l reflect
    let forced := decide (l ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])])
    alternatives := alternatives.map fun cs => cs ++ [ops.normalization words s.wider forced]
  match ops.necessary s words with
  | none => return []
  | some good =>
    let final := good ++ (lowerHistoryFinalCuts p.row).map (fun b => ops.pull b words s.wider)
    return alternatives.map fun cs => (cs ++ final).eraseDups

theorem actual_eval (p : LowerHistoryPath) : eval actualOps p = lowerHistorySourcePremises p := by
  rfl

end RootOps19
end M7SplitSep17

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def bv2 : CertBound := ⟨true,false,⟨⟨(-605239/322621),(452861/322621),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩⟩⟩
noncomputable def bv6 : CertBound := ⟨true,false,⟨⟨(-2396241/3388429),(1794784/3388429),(0),(0)⟩,⟨(247/649),(1/649),(0),(0)⟩,⟨(177/454),(-1/454),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv11 : CertBound := ⟨true,false,⟨⟨(-5111577/15657181),(3840568/15657181),(0),(0)⟩,⟨(483/1318),(1/1318),(0),(0)⟩,⟨(383/1033),(-1/1033),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv13 : CertBound := ⟨true,false,⟨⟨(-271911/1001627),(203584/1001627),(0),(0)⟩,⟨(446/1177),(1/1177),(0),(0)⟩,⟨(651/1702),(-1/1702),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv20 : CertBound := ⟨true,false,⟨⟨(-8845164/47149609),(6653521/47149609),(0),(0)⟩,⟨(797/2221),(1/2221),(0),(0)⟩,⟨(667/1846),(-1/1846),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩⟩⟩
noncomputable def bv26 : CertBound := ⟨true,false,⟨⟨(-25544163/190658063),(19094857/190658063),(0),(0)⟩,⟨(856/2341),(1/2341),(0),(0)⟩,⟨(1301/3541),(-1/3541),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv42 : CertBound := ⟨true,false,⟨⟨(-21593634/271232629),(16126691/271232629),(0),(0)⟩,⟨(1398/3901),(1/3901),(0),(0)⟩,⟨(2173/6046),(-1/6046),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv43 : CertBound := ⟨true,false,⟨⟨(-27041/364702),(168601/1094106),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩⟩⟩
noncomputable def bv175 : CertBound := ⟨true,false,⟨⟨(3023864/142697685),(8765033/1426976850),(0),(0)⟩,⟨(713/1991),(1/5973),(0),(0)⟩,⟨(112/311),(-1/933),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv195 : CertBound := ⟨true,false,⟨⟨(194269963/5454255300),(2189251/218170212),(0),(0)⟩,⟨(439/1202),(1/3606),(0),(0)⟩,⟨(66/179),(-1/537),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv220 : CertBound := ⟨true,false,⟨⟨(46348286/642787275),(4919669/257114910),(0),(0)⟩,⟨(231/611),(1/1833),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv249 : CertBound := ⟨true,false,⟨⟨(17288019/81914300),(23104949/409571500),(0),(0)⟩,⟨(93/262),(1/262),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv258 : CertBound := ⟨true,false,⟨⟨(12374850333/44281430000),(0),(0),(547966053/44281430000)⟩,⟨(1859/5158),(0),(0),(1/5158)⟩,⟨(63/170),(0),(0),(-1/510)⟩,⟨(725/2602),(0),(0),(1/2602)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv260 : CertBound := ⟨true,false,⟨⟨(31/100),(0),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv272 : CertBound := ⟨true,false,⟨⟨(33285470319/67820291500),(-327225429/33910145750),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(2747/7501),(-1/7501),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv274 : CertBound := ⟨true,false,⟨⟨(8164501/16382860),(11119731/81914300),(0),(0)⟩,⟨(93/262),(1/262),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv282 : CertBound := ⟨true,false,⟨⟨(7/10),(0),(0),(1/70)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv287 : CertBound := ⟨true,false,⟨⟨(14844131850/16611163283),(-22622450/16611163283),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(553/1429),(1/1429),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv291 : CertBound := ⟨true,false,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv294 : CertBound := ⟨true,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv419 : CertBound := ⟨true,true,⟨⟨(11/47),(0),(0),(4/329)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv430 : CertBound := ⟨true,true,⟨⟨(3418287291/5478244850),(-26216794/8217367275),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),(0),(0)⟩,⟨(-1/2),(1/2),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv441 : CertBound := ⟨true,true,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv732 : CertBound := ⟨false,false,⟨⟨(15/134),(0),(0),(23/4690)⟩,⟨(3/10),(0),(0),(1/70)⟩,⟨(251/670),(0),(0),(-1/670)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv769 : CertBound := ⟨false,false,⟨⟨(1101/6157),(0),(0),(128/6157)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(105/262),(0),(0),(-1/262)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv774 : CertBound := ⟨false,false,⟨⟨(41/185),(0),(0),(32/1295)⟩,⟨(3/10),(0),(0),(1/70)⟩,⟨(29/74),(0),(0),(-1/222)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv784 : CertBound := ⟨false,false,⟨⟨(13766/50713),(29019/50713),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv795 : CertBound := ⟨false,false,⟨⟨(1011/3145),(0),(0),(-166/3145)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(457/1258),(0),(0),(-1/1258)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv806 : CertBound := ⟨false,false,⟨⟨(13/34),(0),(0),(-7/170)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(63/170),(0),(0),(-1/510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv810 : CertBound := ⟨false,false,⟨⟨(43/94),(0),(0),(37/658)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv811 : CertBound := ⟨false,false,⟨⟨(437151/916486),(1064107/2749458),(0),(0)⟩,⟨(1991/5521),(1/5521),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv824 : CertBound := ⟨false,false,⟨⟨(3418287291/5478244850),(-26216794/8217367275),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv833 : CertBound := ⟨false,false,⟨⟨(7/10),(0),(0),(1/70)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv837 : CertBound := ⟨false,false,⟨⟨(16971/22607),(33730/22607),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv851 : CertBound := ⟨false,false,⟨⟨(13/10),(0),(0),(9/70)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv852 : CertBound := ⟨false,false,⟨⟨(123317000/92840319),(-6536000/278520957),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(1809/6094),(1/6094),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv856 : CertBound := ⟨false,false,⟨⟨(3/2),(0),(0),(1/10)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv858 : CertBound := ⟨false,false,⟨⟨(669/370),0,0,(109/7770)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
noncomputable def bv865 : CertBound := ⟨false,false,⟨⟨(443751/178450),0,0,(4831/178450)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv903 : CertBound := ⟨false,true,⟨⟨(-901820/4598113),(736524/4598113),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
noncomputable def bv904 : CertBound := ⟨false,true,⟨⟨(-20157/109727),(49327/329181),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
noncomputable def bv905 : CertBound := ⟨false,true,⟨⟨(-139303/773638),(57201/386819),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(15/37),(-1/37),0,0⟩⟩⟩
noncomputable def bv1138 : CertBound := ⟨false,true,⟨⟨(12374850333/44281430000),(0),(0),(547966053/44281430000)⟩,⟨(1859/5158),(0),(0),(1/5158)⟩,⟨(63/170),(0),(0),(-1/510)⟩,⟨(725/2602),(0),(0),(1/2602)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv1150 : CertBound := ⟨false,true,⟨⟨(33285470319/67820291500),(-327225429/33910145750),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(2747/7501),(-1/7501),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1165 : CertBound := ⟨false,true,⟨⟨(14844131850/16611163283),(-22622450/16611163283),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(553/1429),(1/1429),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1174 : CertBound := ⟨false,true,⟨⟨(63393/49966),0,0,(4831/349762)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv1176 : CertBound := ⟨false,true,⟨⟨(13/10),(0),(0),(9/70)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv1181 : CertBound := ⟨false,true,⟨⟨(2754444750/2052479143),(-216932250/2052479143),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [bv371,bv843,bv260,bv440] := by
  simpa only [bv371,bv843,bv260,bv440] using BindingNumeric20.initial_base
theorem op115 : lowerHistoryRelaxedGoodness ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [bv3] := by
  decide +kernel
theorem op2 : lowerHistoryNormalization ([2],[3]) false false = bv856 := by
  norm_num [bv856, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op116 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [bv21] := by
  decide +kernel
theorem op84 : lowerHistoryNormalization ([2,1],[3]) true false = bv282 := by
  norm_num [bv282, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op129 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [bv837] := by
  decide +kernel
theorem op86 : lowerHistoryPull (lowerHistoryH2) ([2,1],[3]) true = bv1165 := by
  norm_num [bv1165, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op87 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = bv287 := by
  norm_num [bv287, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op88 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = bv852 := by
  norm_num [bv852, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op89 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = bv811 := by
  norm_num [bv811, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op90 : lowerHistoryPull (lowerHistoryH23) ([2,1],[3]) true = bv1181 := by
  norm_num [bv1181, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op91 : lowerHistoryNormalization ([2,1,1],[3]) true true = bv419 := by
  norm_num [bv419, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
open BindingNumeric20
theorem op130 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [bv784] := by
  decide +kernel
theorem op28 : lowerHistoryNormalization ([2,1,1],[3,1]) false false = bv810 := by
  norm_num [bv810, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op131 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [bv6] := by
  decide +kernel
theorem op30 : lowerHistoryNormalization ([2,1,1,1],[3,1]) false false = bv769 := by
  norm_num [bv769, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op132 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [bv13] := by
  decide +kernel
theorem op32 : lowerHistoryPull (lowerHistoryH7) ([2,1,1,1],[3,1]) false = bv220 := by
  norm_num [bv220, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op33 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1],[3,1]) false = bv769 := by
  norm_num [bv769, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op38 : lowerHistoryNormalization ([2,1],[3,1]) false false = bv851 := by
  norm_num [bv851, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op133 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1],[3,1]) = some [bv2] := by
  decide +kernel
theorem op40 : lowerHistoryPull (lowerHistoryH7) ([2,1],[3,1]) false = bv274 := by
  norm_num [bv274, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op41 : lowerHistoryPull (lowerHistoryHN) ([2,1],[3,1]) false = bv851 := by
  norm_num [bv851, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op4 : lowerHistoryNormalization ([2,1],[3]) false false = bv833 := by
  norm_num [bv833, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def path676 : LowerHistoryPath := ⟨.right,82,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩
noncomputable def raw676 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv769],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv769]]
noncomputable def expected676 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv220],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv220]]
theorem structural676 (ops : RootOps19.SourceOps) (b3 b6 b13 b21 b220 b260 b282 b287 b371 b419 b440 b769 b784 b810 b811 b837 b843 b852 b856 b1165 b1181 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h115 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h116 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h84 : ops.normalization ([2,1],[3]) true false = b282)
    (h129 : ops.necessary ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h86 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (h87 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = b287)
    (h88 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = b852)
    (h89 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = b811)
    (h90 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (h91 : ops.normalization ([2,1,1],[3]) true true = b419)
    (h130 : ops.necessary ⟨⟨([3,1,3,1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (h28 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (h131 : ops.necessary ⟨⟨([3,1,3,1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (h30 : ops.normalization ([2,1,1,1],[3,1]) false false = b769)
    (h132 : ops.necessary ⟨⟨([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [b13])
    (h32 : ops.pull (lowerHistoryH7) ([2,1,1,1],[3,1]) false = b220)
    (h33 : ops.pull (lowerHistoryHN) ([2,1,1,1],[3,1]) false = b769)
    : RootOps19.eval ops path676 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b769],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b769]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path676, h0, h115, h2, h116, h84, h129, h86, h87, h88, h89, h90, h91, h130, h28, h131, h30, h132, h32, h33, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource676 : lowerHistorySourcePremises path676 = raw676.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural676 RootOps19.actualOps bv3 bv6 bv13 bv21 bv220 bv260 bv282 bv287 bv371 bv419 bv440 bv769 bv784 bv810 bv811 bv837 bv843 bv852 bv856 bv1165 bv1181 op0 op115 op2 op116 op84 op129 op86 op87 op88 op89 op90 op91 op130 op28 op131 op30 op132 op32 op33
theorem dedup676 : raw676.map List.eraseDups = expected676 := by
  decide +kernel
theorem source676 : lowerHistorySourcePremises path676 = expected676 := (rawSource676).trans (dedup676)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option linter.all false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
open Freiman
namespace M7SplitSep17
namespace BoundCompact16
set_option maxRecDepth 30000

def emptyBound : CertBound :=
  ⟨true,false,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

theorem bound_of_option (id : ℕ) (target : CertBound)
    (h : lowerHistoryBounds[id - 1]? = some target) :
    lowerHistoryBound id = target := by
  unfold lowerHistoryBound
  exact (congrArg (fun o : Option CertBound => o.getD emptyBound) h).trans rfl

theorem size01 : lowerHistoryBounds01.size = 200 := by rfl
theorem size02 : lowerHistoryBounds02.size = 200 := by rfl
theorem size03 : lowerHistoryBounds03.size = 200 := by rfl
theorem size04 : lowerHistoryBounds04.size = 200 := by rfl
theorem size05 : lowerHistoryBounds05.size = 200 := by rfl

theorem global_to_chunk1 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[i]? = lowerHistoryBounds01[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02)
    (by simp only [Array.size_append, size01, size02]; omega)]
  exact Array.getElem?_append_left (by rw [size01]; omega)

theorem global_to_chunk2 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[200 + i]? = lowerHistoryBounds02[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02)
    (by simp only [Array.size_append, size01, size02]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01) (by rw [size01]; omega), size01]
  exact congrArg (fun j => lowerHistoryBounds02[j]?) (by omega)

theorem global_to_chunk3 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[400 + i]? = lowerHistoryBounds03[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02)
    (by simp only [Array.size_append, size01, size02]; omega)]
  simp only [Array.size_append, size01, size02]
  exact congrArg (fun j => lowerHistoryBounds03[j]?) (by omega)

theorem global_to_chunk4 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[600 + i]? = lowerHistoryBounds04[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  simp only [Array.size_append, size01, size02, size03]
  exact congrArg (fun j => lowerHistoryBounds04[j]?) (by omega)

theorem global_to_chunk5 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[800 + i]? = lowerHistoryBounds05[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04]
  exact congrArg (fun j => lowerHistoryBounds05[j]?) (by omega)

theorem global_to_chunk6 (i : ℕ) :
    lowerHistoryBounds[1000 + i]? = lowerHistoryBounds06[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04, size05]
  exact congrArg (fun j => lowerHistoryBounds06[j]?) (by omega)

end BoundCompact16
namespace PremiseCompact50

variable {α : Type} (a b c d e f : Array α)
  (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200)
  (hd : d.size = 200) (he : e.size = 200)
include ha hb hc hd he

theorem lookup_chunk1 (i : ℕ) (hi : i < 200) :
    (a ++ b ++ c ++ d ++ e ++ f)[i]? = a[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e)
    (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d)
    (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c)
    (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b)
    (by simp only [Array.size_append, ha, hb]; omega)]
  exact Array.getElem?_append_left (xs := a) (by omega)

theorem lookup_chunk2 (i : ℕ) (hi : i < 200) :
    (a ++ b ++ c ++ d ++ e ++ f)[200 + i]? = b[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e)
    (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d)
    (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c)
    (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b)
    (by simp only [Array.size_append, ha, hb]; omega)]
  rw [Array.getElem?_append_right (xs := a) (by omega), ha]
  exact congrArg (fun j => b[j]?) (by omega)

end PremiseCompact50
namespace WitnessCompact16
set_option maxRecDepth 30000

def witnessShape (w : CertWitness) : CertBound × CertBound × CertRectangle :=
  (w.lowerBound, w.upperBound, w.rectangle)

def emptyWitness : CertWitness :=
  ⟨lowerHistoryBound 0, lowerHistoryBound 0, ⟨0,1,0,1⟩,
    fun _ _ => ⟨0,0,0,0⟩, fun _ _ => 0⟩

theorem lowerHistoryWitness_def (id : ℕ) :
    lowerHistoryWitness id =
      (lowerHistoryWitnesses[id - 1]?).getD emptyWitness := by
  rfl

theorem projections_of_shape (w : CertWitness) (l u : CertBound)
    (r : CertRectangle) (h : witnessShape w = (l, u, r)) :
    w.lowerBound = l ∧ w.upperBound = u ∧ w.rectangle = r := by
  simpa only [witnessShape, Prod.mk.injEq] using h

theorem shape_of_global_option (id : ℕ)
    (target : CertBound × CertBound × CertRectangle)
    (h : (lowerHistoryWitnesses[id - 1]?).map witnessShape = some target) :
    witnessShape (lowerHistoryWitness id) = target := by
  have hs : witnessShape ((lowerHistoryWitnesses[id - 1]?).getD emptyWitness) =
      target := by
    cases ho : lowerHistoryWitnesses[id - 1]? <;> simp_all
  exact (congrArg witnessShape (lowerHistoryWitness_def id)).trans hs

theorem projection_of_global_option (id : ℕ)
    (l u : CertBound) (r : CertRectangle)
    (h : (lowerHistoryWitnesses[id - 1]?).map witnessShape = some (l, u, r)) :
    (lowerHistoryWitness id).lowerBound = l ∧
    (lowerHistoryWitness id).upperBound = u ∧
    (lowerHistoryWitness id).rectangle = r := by
  exact projections_of_shape _ _ _ _ (shape_of_global_option id (l, u, r) h)

theorem size01 : lowerHistoryWitnesses01.size = 200 := by rfl
theorem size02 : lowerHistoryWitnesses02.size = 200 := by rfl
theorem size03 : lowerHistoryWitnesses03.size = 200 := by rfl
theorem size04 : lowerHistoryWitnesses04.size = 200 := by rfl
theorem size05 : lowerHistoryWitnesses05.size = 200 := by rfl

theorem global_to_chunk5 (i : ℕ) (hi : i < 200) :
    lowerHistoryWitnesses[800 + i]? = lowerHistoryWitnesses05[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04]
  exact congrArg (fun j => lowerHistoryWitnesses05[j]?) (by omega)

theorem global_to_chunk6 (i : ℕ) :
    lowerHistoryWitnesses[1000 + i]? = lowerHistoryWitnesses06[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04, size05]
  exact congrArg (fun j => lowerHistoryWitnesses06[j]?) (by omega)

end WitnessCompact16
namespace BindingIds19
set_option Elab.async false
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

def extras (p : LowerHistoryPath) (branch : Nat) : List CertBound :=
  let comp := (lowerHistoryEndpointComparisons p)[branch]?.getD ([],.automatic)
  comp.1 ++ (match comp.2 with | .bound b => [lowerHistoryComplement b] | _ => [])

def residualIds (src ext : List (List Nat)) (r : LowerHistoryRecord) : List Nat :=
  if r.endpointBranch < 0 then src[r.alternative]?.getD []
  else src[r.alternative]?.getD [] ++ ext[r.endpointBranch.toNat]?.getD []

instance survivorDecidable (p : LowerHistoryPath) : Decidable (lowerHistorySurvivor p) := by
  unfold lowerHistorySurvivor
  infer_instance

def recordCheck (p : LowerHistoryPath) (src ext : List (List Nat))
    (wids : Nat → Nat × Nat) (preIDs : Nat → List Nat) (np nw : Nat) (r : LowerHistoryRecord) : Bool :=
  if r.survivor then decide (lowerHistorySurvivor p ∧ r.alternative = 0) else
  decide (0 < r.premiseId ∧ r.premiseId ≤ np ∧
    0 < r.witnessId ∧ r.witnessId ≤ nw ∧
    (r.endpointBranch < 0 ∨ r.endpointBranch.toNat < ext.length) ∧
    (preIDs r.premiseId).toFinset = (residualIds src ext r).toFinset ∧
    (wids r.witnessId).1 ∈ preIDs r.premiseId ∧
    (wids r.witnessId).2 ∈ preIDs r.premiseId)

theorem map_getD (xs : List (List Nat)) (i : Nat) :
    ((xs.map (List.map lowerHistoryBound))[i]?).getD [] =
      (xs[i]?.getD []).map lowerHistoryBound := by
  cases h : xs[i]? <;> simp [List.getElem?_map, h]

theorem mapped_finset_congr (a b : List Nat) (h : a.toFinset = b.toFinset) :
    (a.map lowerHistoryBound).toFinset = (b.map lowerHistoryBound).toFinset := by
  have hm : ∀ x, x ∈ a ↔ x ∈ b := by
    intro x
    simpa only [List.mem_toFinset] using
      (Iff.of_eq (congrArg (fun s : Finset Nat => x ∈ s) h))
  ext x
  simp only [List.mem_toFinset, List.mem_map, hm]

theorem residual_values (p : LowerHistoryPath) (src ext : List (List Nat))
    (r : LowerHistoryRecord)
    (hs : lowerHistorySourcePremises p = src.map (List.map lowerHistoryBound))
    (he : (List.range ext.length).map (extras p) = ext.map (List.map lowerHistoryBound))
    (hb : r.endpointBranch < 0 ∨ r.endpointBranch.toNat < ext.length) :
    (lowerHistoryResidual p r.alternative r.endpointBranch).toFinset =
      ((residualIds src ext r).map lowerHistoryBound).toFinset := by
  by_cases hn : r.endpointBranch < 0
  · simp only [lowerHistoryResidual, residualIds, hn, ↓reduceIte, hs, map_getD]
  · have hbi : r.endpointBranch.toNat < ext.length := hb.resolve_left hn
    have hget : extras p r.endpointBranch.toNat =
        (ext[r.endpointBranch.toNat]?.getD []).map lowerHistoryBound := by
      have hm := congrArg (fun bs : List (List CertBound) => bs[r.endpointBranch.toNat]?.getD []) he
      simpa [List.getElem?_map, List.getElem?_range, hbi, map_getD] using hm
    have hdup (bs : List CertBound) : bs.eraseDups.toFinset = bs.toFinset := by
      ext b
      simp only [List.mem_toFinset, List.mem_eraseDups]
    simp only [lowerHistoryResidual, hn, ↓reduceIte]
    rw [hdup]
    rw [List.append_assoc]
    change ((lowerHistorySourcePremises p)[r.alternative]?.getD [] ++
      extras p r.endpointBranch.toNat).toFinset = _
    rw [hs, map_getD, hget]
    simp only [residualIds, hn, ↓reduceIte, List.map_append]

theorem recordCheck_sound (p : LowerHistoryPath) (src ext : List (List Nat))
    (wids : Nat → Nat × Nat) (preIDs : Nat → List Nat) (np nw : Nat) (r : LowerHistoryRecord)
    (hz : lowerHistoryPremises.size = np ∧ lowerHistoryWitnesses.size = nw)
    (hs : lowerHistorySourcePremises p = src.map (List.map lowerHistoryBound))
    (he : (List.range ext.length).map (extras p) = ext.map (List.map lowerHistoryBound))
    (hprem : r.survivor = false → lowerHistoryPremise r.premiseId =
      (preIDs r.premiseId).map lowerHistoryBound)
    (hw : r.survivor = false →
      (lowerHistoryWitness r.witnessId).lowerBound = lowerHistoryBound (wids r.witnessId).1 ∧
      (lowerHistoryWitness r.witnessId).upperBound = lowerHistoryBound (wids r.witnessId).2 ∧
      (lowerHistoryWitness r.witnessId).rectangle = p.rectangle)
    (hc : recordCheck p src ext wids preIDs np nw r = true) : lowerHistoryRecordBinding p r := by
  cases hr : r.survivor
  · simp only [recordCheck, hr, Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at hc
    rcases hc with ⟨hp, hps, hwpos, hws, hb, hf, hl, hu⟩
    have hres := residual_values p src ext r hs he hb
    have hw' := hw hr
    have hpre := hprem hr
    simp only [lowerHistoryRecordBinding, hr, Bool.false_eq_true, ↓reduceIte]
    refine ⟨hp, ?_, hwpos, ?_, ?_, ?_, ?_, hw'.2.2⟩
    · rwa [hz.1]
    · rwa [hz.2]
    · rw [hpre]
      exact (mapped_finset_congr _ _ hf).trans hres.symm
    · rw [hw'.1, hpre]
      exact List.mem_map.mpr ⟨_, hl, rfl⟩
    · rw [hw'.2.1, hpre]
      exact List.mem_map.mpr ⟨_, hu, rfl⟩
  · simpa only [recordCheck, lowerHistoryRecordBinding, hr, ↓reduceIte, decide_eq_true_eq] using hc

theorem pathBinding_from_ids (p : LowerHistoryPath) (src ext : List (List Nat))
    (rs : List LowerHistoryRecord) (wids : Nat → Nat × Nat) (preIDs : Nat → List Nat) (np nw : Nat)
    (hz : lowerHistoryPremises.size = np ∧ lowerHistoryWitnesses.size = nw)
    (hs : lowerHistorySourcePremises p = src.map (List.map lowerHistoryBound))
    (he : (List.range ext.length).map (extras p) = ext.map (List.map lowerHistoryBound))
    (hrs : lowerHistoryRecordsFor p = rs) (hlen : p.alternatives = src.length)
    (hprem : ∀ r ∈ rs, r.survivor = false → lowerHistoryPremise r.premiseId =
      (preIDs r.premiseId).map lowerHistoryBound)
    (hw : ∀ r ∈ rs, r.survivor = false →
      (lowerHistoryWitness r.witnessId).lowerBound = lowerHistoryBound (wids r.witnessId).1 ∧
      (lowerHistoryWitness r.witnessId).upperBound = lowerHistoryBound (wids r.witnessId).2 ∧
      (lowerHistoryWitness r.witnessId).rectangle = p.rectangle)
    (hcheck : rs.all (recordCheck p src ext wids preIDs np nw) = true)
    (hcover : lowerHistoryRecordCoverage p) : lowerHistoryPathBinding p := by
  refine ⟨?_, ?_, hcover⟩
  · simpa [hs] using hlen
  · intro r hr
    rw [hrs] at hr
    exact recordCheck_sound p src ext wids preIDs np nw r hz hs he (hprem r hr) (hw r hr)
      ((List.all_eq_true.mp hcheck) r hr)
end BindingIds19
namespace BatchCoverage15

def coverageCheck (p : LowerHistoryPath) (rs : List LowerHistoryRecord) (ai : ℕ) : Bool :=
  rs.any (fun r => decide (r.alternative = ai ∧ r.endpointBranch < 0)) ||
    (decide (p.catalog ≠ .initial ∧ p.row ≠ 4) &&
      ((lowerHistoryEndpointComparisons p).zipIdx.all fun (cg,bi) =>
        decide (cg.2 = .automatic) || rs.any fun r =>
          decide (r.alternative = ai ∧ r.endpointBranch = (bi : ℤ) ∧ r.survivor = false)))

theorem coverage_sound (p : LowerHistoryPath) (rs : List LowerHistoryRecord)
    (hrs : lowerHistoryRecordsFor p = rs)
    (hlen : p.alternatives = (lowerHistorySourcePremises p).length)
    (hcheck : (List.range p.alternatives).all (coverageCheck p rs) = true) :
    lowerHistoryRecordCoverage p := by
  intro ai hai
  have hai' : ai < p.alternatives := by rwa [hlen]
  have ha := (List.all_eq_true.mp hcheck) ai (List.mem_range.mpr hai')
  simp only [coverageCheck, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true,
    List.all_eq_true, decide_eq_true_eq] at ha
  rcases ha with ha | ⟨⟨hi,hr⟩,hc⟩
  · left
    obtain ⟨r,hm,halt,hbranch⟩ := ha
    exact ⟨r,Eq.mpr (congrArg (fun zs : List LowerHistoryRecord => r ∈ zs) hrs) hm,
      halt,hbranch⟩
  · right
    refine ⟨hi,hr,?_⟩
    intro bi cs g hget hna
    have hm : ((cs,g),bi) ∈ (lowerHistoryEndpointComparisons p).zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr hget
    rcases hc ((cs,g),bi) hm with hauto | hw
    · exact False.elim (hna hauto)
    · obtain ⟨r,hm,hrest⟩ := hw
      exact ⟨r,Eq.mpr (congrArg (fun zs : List LowerHistoryRecord => r ∈ zs) hrs) hm,hrest⟩

end BatchCoverage15
namespace BatchLookup20
theorem nonleft_catalogs :
  (∀ r ∈ lowerHistoryRecordsR.toList, r.catalog ≠ .left) ∧
  (∀ r ∈ lowerHistoryRecordsM.toList, r.catalog ≠ .left) ∧
  (∀ r ∈ lowerHistoryRecordsX.toList, r.catalog ≠ .left) ∧
  (∀ r ∈ lowerHistoryRecordsH.toList, r.catalog ≠ .left) := by
  decide +kernel
theorem filter_nonleft (xs : List LowerHistoryRecord)
    (h : ∀ r ∈ xs, r.catalog ≠ .left) (id : Nat) :
    xs.filter (fun r => decide (r.catalog = .left ∧ r.pathId = id)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro r hr
  simpa only [decide_eq_true_eq] using (show ¬ (r.catalog = .left ∧ r.pathId = id) from fun hri => h r hr hri.1)
theorem left_filter (id : Nat) :
    lowerHistoryRecordsFor (⟨.left,id,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) =
      lowerHistoryRecordsL.toList.filter (fun r => decide (r.catalog = .left ∧ r.pathId = id)) := by
  unfold lowerHistoryRecordsFor lowerHistoryRecords
  simp only [Array.toList_append, List.filter_append]
  rw [filter_nonleft _ nonleft_catalogs.1,
      filter_nonleft _ nonleft_catalogs.2.1,
      filter_nonleft _ nonleft_catalogs.2.2.1,
      filter_nonleft _ nonleft_catalogs.2.2.2]
  simp only [List.append_nil]
end BatchLookup20
theorem premise_size : lowerHistoryPremises.size = 1025 := by
  simp only [lowerHistoryPremises, Array.size_append]
  rfl
theorem witness_size : lowerHistoryWitnesses.size = 1194 := by
  simp only [lowerHistoryWitnesses, Array.size_append]
  rfl
end M7SplitSep17

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
theorem bound2 : lowerHistoryBound 2 = bv2 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[1]? = some bv2 := Eq.refl (some bv2)
  exact (BoundCompact16.global_to_chunk1 1 (by decide)).trans hl
theorem bound3 : lowerHistoryBound 3 = bv3 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[2]? = some bv3 := Eq.refl (some bv3)
  exact (BoundCompact16.global_to_chunk1 2 (by decide)).trans hl
theorem bound6 : lowerHistoryBound 6 = bv6 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[5]? = some bv6 := Eq.refl (some bv6)
  exact (BoundCompact16.global_to_chunk1 5 (by decide)).trans hl
theorem bound11 : lowerHistoryBound 11 = bv11 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[10]? = some bv11 := Eq.refl (some bv11)
  exact (BoundCompact16.global_to_chunk1 10 (by decide)).trans hl
theorem bound13 : lowerHistoryBound 13 = bv13 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[12]? = some bv13 := Eq.refl (some bv13)
  exact (BoundCompact16.global_to_chunk1 12 (by decide)).trans hl
theorem bound20 : lowerHistoryBound 20 = bv20 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[19]? = some bv20 := Eq.refl (some bv20)
  exact (BoundCompact16.global_to_chunk1 19 (by decide)).trans hl
theorem bound21 : lowerHistoryBound 21 = bv21 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[20]? = some bv21 := Eq.refl (some bv21)
  exact (BoundCompact16.global_to_chunk1 20 (by decide)).trans hl
theorem bound26 : lowerHistoryBound 26 = bv26 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[25]? = some bv26 := Eq.refl (some bv26)
  exact (BoundCompact16.global_to_chunk1 25 (by decide)).trans hl
theorem bound42 : lowerHistoryBound 42 = bv42 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[41]? = some bv42 := Eq.refl (some bv42)
  exact (BoundCompact16.global_to_chunk1 41 (by decide)).trans hl
theorem bound43 : lowerHistoryBound 43 = bv43 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[42]? = some bv43 := Eq.refl (some bv43)
  exact (BoundCompact16.global_to_chunk1 42 (by decide)).trans hl
theorem bound175 : lowerHistoryBound 175 = bv175 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[174]? = some bv175 := Eq.refl (some bv175)
  exact (BoundCompact16.global_to_chunk1 174 (by decide)).trans hl
theorem bound195 : lowerHistoryBound 195 = bv195 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[194]? = some bv195 := Eq.refl (some bv195)
  exact (BoundCompact16.global_to_chunk1 194 (by decide)).trans hl
theorem bound220 : lowerHistoryBound 220 = bv220 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[19]? = some bv220 := Eq.refl (some bv220)
  exact (BoundCompact16.global_to_chunk2 19 (by decide)).trans hl
theorem bound249 : lowerHistoryBound 249 = bv249 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[48]? = some bv249 := Eq.refl (some bv249)
  exact (BoundCompact16.global_to_chunk2 48 (by decide)).trans hl
theorem bound258 : lowerHistoryBound 258 = bv258 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[57]? = some bv258 := Eq.refl (some bv258)
  exact (BoundCompact16.global_to_chunk2 57 (by decide)).trans hl
theorem bound260 : lowerHistoryBound 260 = bv260 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[59]? = some bv260 := Eq.refl (some bv260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hl
theorem bound272 : lowerHistoryBound 272 = bv272 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[71]? = some bv272 := Eq.refl (some bv272)
  exact (BoundCompact16.global_to_chunk2 71 (by decide)).trans hl
theorem bound274 : lowerHistoryBound 274 = bv274 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[73]? = some bv274 := Eq.refl (some bv274)
  exact (BoundCompact16.global_to_chunk2 73 (by decide)).trans hl
theorem bound282 : lowerHistoryBound 282 = bv282 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[81]? = some bv282 := Eq.refl (some bv282)
  exact (BoundCompact16.global_to_chunk2 81 (by decide)).trans hl
theorem bound287 : lowerHistoryBound 287 = bv287 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[86]? = some bv287 := Eq.refl (some bv287)
  exact (BoundCompact16.global_to_chunk2 86 (by decide)).trans hl
theorem bound291 : lowerHistoryBound 291 = bv291 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[90]? = some bv291 := Eq.refl (some bv291)
  exact (BoundCompact16.global_to_chunk2 90 (by decide)).trans hl
theorem bound294 : lowerHistoryBound 294 = bv294 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[93]? = some bv294 := Eq.refl (some bv294)
  exact (BoundCompact16.global_to_chunk2 93 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound419 : lowerHistoryBound 419 = bv419 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[18]? = some bv419 := Eq.refl (some bv419)
  exact (BoundCompact16.global_to_chunk3 18 (by decide)).trans hl
theorem bound430 : lowerHistoryBound 430 = bv430 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[29]? = some bv430 := Eq.refl (some bv430)
  exact (BoundCompact16.global_to_chunk3 29 (by decide)).trans hl
theorem bound440 : lowerHistoryBound 440 = bv440 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[39]? = some bv440 := Eq.refl (some bv440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hl
theorem bound441 : lowerHistoryBound 441 = bv441 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[40]? = some bv441 := Eq.refl (some bv441)
  exact (BoundCompact16.global_to_chunk3 40 (by decide)).trans hl
theorem bound732 : lowerHistoryBound 732 = bv732 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[131]? = some bv732 := Eq.refl (some bv732)
  exact (BoundCompact16.global_to_chunk4 131 (by decide)).trans hl
theorem bound769 : lowerHistoryBound 769 = bv769 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[168]? = some bv769 := Eq.refl (some bv769)
  exact (BoundCompact16.global_to_chunk4 168 (by decide)).trans hl
theorem bound774 : lowerHistoryBound 774 = bv774 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[173]? = some bv774 := Eq.refl (some bv774)
  exact (BoundCompact16.global_to_chunk4 173 (by decide)).trans hl
theorem bound784 : lowerHistoryBound 784 = bv784 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[183]? = some bv784 := Eq.refl (some bv784)
  exact (BoundCompact16.global_to_chunk4 183 (by decide)).trans hl
theorem bound795 : lowerHistoryBound 795 = bv795 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[194]? = some bv795 := Eq.refl (some bv795)
  exact (BoundCompact16.global_to_chunk4 194 (by decide)).trans hl
theorem bound806 : lowerHistoryBound 806 = bv806 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[5]? = some bv806 := Eq.refl (some bv806)
  exact (BoundCompact16.global_to_chunk5 5 (by decide)).trans hl
theorem bound810 : lowerHistoryBound 810 = bv810 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[9]? = some bv810 := Eq.refl (some bv810)
  exact (BoundCompact16.global_to_chunk5 9 (by decide)).trans hl
theorem bound811 : lowerHistoryBound 811 = bv811 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[10]? = some bv811 := Eq.refl (some bv811)
  exact (BoundCompact16.global_to_chunk5 10 (by decide)).trans hl
theorem bound824 : lowerHistoryBound 824 = bv824 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[23]? = some bv824 := Eq.refl (some bv824)
  exact (BoundCompact16.global_to_chunk5 23 (by decide)).trans hl
theorem bound833 : lowerHistoryBound 833 = bv833 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[32]? = some bv833 := Eq.refl (some bv833)
  exact (BoundCompact16.global_to_chunk5 32 (by decide)).trans hl
theorem bound837 : lowerHistoryBound 837 = bv837 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[36]? = some bv837 := Eq.refl (some bv837)
  exact (BoundCompact16.global_to_chunk5 36 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound851 : lowerHistoryBound 851 = bv851 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[50]? = some bv851 := Eq.refl (some bv851)
  exact (BoundCompact16.global_to_chunk5 50 (by decide)).trans hl
theorem bound852 : lowerHistoryBound 852 = bv852 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[51]? = some bv852 := Eq.refl (some bv852)
  exact (BoundCompact16.global_to_chunk5 51 (by decide)).trans hl
theorem bound856 : lowerHistoryBound 856 = bv856 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[55]? = some bv856 := Eq.refl (some bv856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hl
theorem bound858 : lowerHistoryBound 858 = bv858 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[57]? = some bv858 := Eq.refl (some bv858)
  exact (BoundCompact16.global_to_chunk5 57 (by decide)).trans hl
theorem bound865 : lowerHistoryBound 865 = bv865 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[64]? = some bv865 := Eq.refl (some bv865)
  exact (BoundCompact16.global_to_chunk5 64 (by decide)).trans hl
theorem bound903 : lowerHistoryBound 903 = bv903 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[102]? = some bv903 := Eq.refl (some bv903)
  exact (BoundCompact16.global_to_chunk5 102 (by decide)).trans hl
theorem bound904 : lowerHistoryBound 904 = bv904 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[103]? = some bv904 := Eq.refl (some bv904)
  exact (BoundCompact16.global_to_chunk5 103 (by decide)).trans hl
theorem bound905 : lowerHistoryBound 905 = bv905 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[104]? = some bv905 := Eq.refl (some bv905)
  exact (BoundCompact16.global_to_chunk5 104 (by decide)).trans hl
theorem bound1138 : lowerHistoryBound 1138 = bv1138 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[137]? = some bv1138 := Eq.refl (some bv1138)
  exact (BoundCompact16.global_to_chunk6 137).trans hl
theorem bound1150 : lowerHistoryBound 1150 = bv1150 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[149]? = some bv1150 := Eq.refl (some bv1150)
  exact (BoundCompact16.global_to_chunk6 149).trans hl
theorem bound1165 : lowerHistoryBound 1165 = bv1165 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[164]? = some bv1165 := Eq.refl (some bv1165)
  exact (BoundCompact16.global_to_chunk6 164).trans hl
theorem bound1174 : lowerHistoryBound 1174 = bv1174 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[173]? = some bv1174 := Eq.refl (some bv1174)
  exact (BoundCompact16.global_to_chunk6 173).trans hl
theorem bound1176 : lowerHistoryBound 1176 = bv1176 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[175]? = some bv1176 := Eq.refl (some bv1176)
  exact (BoundCompact16.global_to_chunk6 175).trans hl
theorem bound1181 : lowerHistoryBound 1181 = bv1181 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[180]? = some bv1181 := Eq.refl (some bv1181)
  exact (BoundCompact16.global_to_chunk6 180).trans hl
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
open Freiman
namespace M7ContinueSep17.CatalogueGeneral

def catalogRecords : LowerHistoryCatalog → List LowerHistoryRecord
  | .left => lowerHistoryRecordsL.toList
  | .right => lowerHistoryRecordsR.toList
  | .mixed => lowerHistoryRecordsM.toList
  | .rightMixed => lowerHistoryRecordsX.toList
  | .initial => lowerHistoryRecordsH.toList

theorem records_catalog (c : LowerHistoryCatalog) :
    ∀ r ∈ catalogRecords c, r.catalog = c := by
  cases c <;> decide +kernel

theorem filter_other (c d : LowerHistoryCatalog) (hne : c ≠ d) (id : Nat) :
    (catalogRecords c).filter (fun r => decide (r.catalog = d ∧ r.pathId = id)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro r hr
  simp only [decide_eq_true_eq]
  intro h
  exact hne ((records_catalog c r hr).symm.trans h.1)

theorem records_partition : lowerHistoryRecords.toList =
    catalogRecords .left ++ catalogRecords .right ++ catalogRecords .mixed ++
    catalogRecords .rightMixed ++ catalogRecords .initial := by
  simp only [lowerHistoryRecords, Array.toList_append, catalogRecords]

theorem records_for_catalog (p : LowerHistoryPath) : lowerHistoryRecordsFor p =
    (catalogRecords p.catalog).filter (fun r => decide (r.catalog = p.catalog ∧ r.pathId = p.id)) := by
  unfold lowerHistoryRecordsFor
  rw [records_partition]
  simp only [List.filter_append]
  cases hc : p.catalog
  · rw [filter_other .right .left (by decide), filter_other .mixed .left (by decide),
      filter_other .rightMixed .left (by decide), filter_other .initial .left (by decide)]
    simp only [List.append_nil]
  · rw [filter_other .left .right (by decide), filter_other .mixed .right (by decide),
      filter_other .rightMixed .right (by decide), filter_other .initial .right (by decide)]
    simp only [List.append_nil, List.nil_append]
  · rw [filter_other .left .mixed (by decide), filter_other .right .mixed (by decide),
      filter_other .rightMixed .mixed (by decide), filter_other .initial .mixed (by decide)]
    simp only [List.append_nil, List.nil_append]
  · rw [filter_other .left .rightMixed (by decide), filter_other .right .rightMixed (by decide),
      filter_other .mixed .rightMixed (by decide), filter_other .initial .rightMixed (by decide)]
    simp only [List.append_nil, List.nil_append]
  · rw [filter_other .left .initial (by decide), filter_other .right .initial (by decide),
      filter_other .mixed .initial (by decide), filter_other .rightMixed .initial (by decide)]
    simp only [List.nil_append]
end M7ContinueSep17.CatalogueGeneral

set_option maxRecDepth 100000
open Freiman
namespace M7ContinueSep17.CatalogueGeneral
theorem catalogListR : catalogRecords .right = [
⟨.right,1,0,(-1),false,233,1114⟩,
⟨.right,2,0,(-1),false,154,1126⟩,
⟨.right,3,0,(-1),false,344,638⟩,
⟨.right,4,0,(-1),false,234,770⟩,
⟨.right,5,0,(-1),false,284,674⟩,
⟨.right,5,1,(-1),false,282,674⟩,
⟨.right,5,2,(-1),false,283,674⟩,
⟨.right,5,3,(-1),false,281,674⟩,
⟨.right,6,0,(-1),false,155,1048⟩,
⟨.right,6,1,0,false,152,1020⟩,
⟨.right,6,1,1,false,140,1020⟩,
⟨.right,6,1,2,false,146,544⟩,
⟨.right,6,1,3,false,148,1020⟩,
⟨.right,6,1,4,false,137,1036⟩,
⟨.right,6,1,5,false,134,794⟩,
⟨.right,6,1,6,false,135,530⟩,
⟨.right,6,1,7,false,136,794⟩,
⟨.right,6,1,8,false,150,322⟩,
⟨.right,6,1,9,false,138,302⟩,
⟨.right,6,1,10,false,142,534⟩,
⟨.right,6,1,11,false,143,310⟩,
⟨.right,6,1,12,false,151,1036⟩,
⟨.right,6,1,13,false,139,803⟩,
⟨.right,6,1,14,false,144,538⟩,
⟨.right,6,1,15,false,145,807⟩,
⟨.right,7,0,(-1),false,194,716⟩,
⟨.right,7,1,(-1),false,193,98⟩,
⟨.right,8,0,0,false,90,798⟩,
⟨.right,8,0,1,false,84,183⟩,
⟨.right,8,0,2,false,86,1058⟩,
⟨.right,8,0,3,false,88,252⟩,
⟨.right,8,0,4,false,54,1054⟩,
⟨.right,8,0,5,false,51,193⟩,
⟨.right,8,0,6,false,52,1068⟩,
⟨.right,8,0,7,false,53,262⟩,
⟨.right,8,0,8,false,82,318⟩,
⟨.right,8,0,9,false,76,183⟩,
⟨.right,8,0,10,false,78,1058⟩,
⟨.right,8,0,11,false,79,252⟩,
⟨.right,8,0,12,false,83,811⟩,
⟨.right,8,0,13,false,77,187⟩,
⟨.right,8,0,14,false,80,1062⟩,
⟨.right,8,0,15,false,81,256⟩,
⟨.right,9,0,(-1),false,385,758⟩,
⟨.right,9,1,(-1),false,384,758⟩,
⟨.right,9,2,(-1),false,386,758⟩,
⟨.right,10,0,(-1),false,321,680⟩,
⟨.right,11,0,(-1),false,36,788⟩,
⟨.right,12,0,(-1),false,387,758⟩,
⟨.right,13,0,(-1),false,322,680⟩,
⟨.right,14,0,(-1),false,170,716⟩,
⟨.right,15,0,(-1),false,12,215⟩,
⟨.right,16,0,(-1),false,233,1113⟩,
⟨.right,17,0,(-1),false,154,1125⟩,
⟨.right,18,0,(-1),false,344,637⟩,
⟨.right,19,0,(-1),false,234,769⟩,
⟨.right,20,0,(-1),false,284,673⟩,
⟨.right,20,1,(-1),false,282,673⟩,
⟨.right,20,2,(-1),false,283,673⟩,
⟨.right,20,3,(-1),false,281,673⟩,
⟨.right,21,0,(-1),false,155,1047⟩,
⟨.right,21,1,0,false,152,1019⟩,
⟨.right,21,1,1,false,140,1019⟩,
⟨.right,21,1,2,false,146,543⟩,
⟨.right,21,1,3,false,148,1019⟩,
⟨.right,21,1,4,false,137,1035⟩,
⟨.right,21,1,5,false,134,793⟩,
⟨.right,21,1,6,false,135,529⟩,
⟨.right,21,1,7,false,136,793⟩,
⟨.right,21,1,8,false,150,321⟩,
⟨.right,21,1,9,false,138,301⟩,
⟨.right,21,1,10,false,142,533⟩,
⟨.right,21,1,11,false,143,309⟩,
⟨.right,21,1,12,false,151,1035⟩,
⟨.right,21,1,13,false,139,802⟩,
⟨.right,21,1,14,false,144,537⟩,
⟨.right,21,1,15,false,145,806⟩,
⟨.right,22,0,(-1),false,194,715⟩,
⟨.right,22,1,(-1),false,193,97⟩,
⟨.right,23,0,0,false,90,797⟩,
⟨.right,23,0,1,false,84,182⟩,
⟨.right,23,0,2,false,86,1057⟩,
⟨.right,23,0,3,false,88,251⟩,
⟨.right,23,0,4,false,54,1053⟩,
⟨.right,23,0,5,false,51,192⟩,
⟨.right,23,0,6,false,52,1067⟩,
⟨.right,23,0,7,false,53,261⟩,
⟨.right,23,0,8,false,82,317⟩,
⟨.right,23,0,9,false,76,182⟩,
⟨.right,23,0,10,false,78,1057⟩,
⟨.right,23,0,11,false,79,251⟩,
⟨.right,23,0,12,false,83,810⟩,
⟨.right,23,0,13,false,77,186⟩,
⟨.right,23,0,14,false,80,1061⟩,
⟨.right,23,0,15,false,81,255⟩,
⟨.right,24,0,(-1),false,385,757⟩,
⟨.right,24,1,(-1),false,384,757⟩,
⟨.right,24,2,(-1),false,386,757⟩,
⟨.right,25,0,(-1),false,321,679⟩,
⟨.right,26,0,(-1),false,36,787⟩,
⟨.right,27,0,(-1),false,387,757⟩,
⟨.right,28,0,(-1),false,322,679⟩,
⟨.right,29,0,(-1),false,170,715⟩,
⟨.right,30,0,(-1),false,12,214⟩,
⟨.right,31,0,(-1),false,233,1111⟩,
⟨.right,32,0,(-1),false,154,1123⟩,
⟨.right,33,0,(-1),false,344,635⟩,
⟨.right,34,0,(-1),false,234,767⟩,
⟨.right,35,0,(-1),false,284,671⟩,
⟨.right,35,1,(-1),false,282,671⟩,
⟨.right,35,2,(-1),false,283,671⟩,
⟨.right,35,3,(-1),false,281,671⟩,
⟨.right,36,0,(-1),false,155,1045⟩,
⟨.right,36,1,0,false,152,1017⟩,
⟨.right,36,1,1,false,140,1017⟩,
⟨.right,36,1,2,false,146,541⟩,
⟨.right,36,1,3,false,148,1017⟩,
⟨.right,36,1,4,false,137,1033⟩,
⟨.right,36,1,5,false,134,791⟩,
⟨.right,36,1,6,false,135,527⟩,
⟨.right,36,1,7,false,136,791⟩,
⟨.right,36,1,8,false,150,319⟩,
⟨.right,36,1,9,false,138,299⟩,
⟨.right,36,1,10,false,142,531⟩,
⟨.right,36,1,11,false,143,307⟩,
⟨.right,36,1,12,false,151,1033⟩,
⟨.right,36,1,13,false,139,800⟩,
⟨.right,36,1,14,false,144,535⟩,
⟨.right,36,1,15,false,145,804⟩,
⟨.right,37,0,(-1),false,194,713⟩,
⟨.right,37,1,(-1),false,193,95⟩,
⟨.right,38,0,0,false,90,795⟩,
⟨.right,38,0,1,false,84,180⟩,
⟨.right,38,0,2,false,86,1055⟩,
⟨.right,38,0,3,false,88,249⟩,
⟨.right,38,0,4,false,54,1051⟩,
⟨.right,38,0,5,false,51,190⟩,
⟨.right,38,0,6,false,52,1065⟩,
⟨.right,38,0,7,false,53,259⟩,
⟨.right,38,0,8,false,82,315⟩,
⟨.right,38,0,9,false,76,180⟩,
⟨.right,38,0,10,false,78,1055⟩,
⟨.right,38,0,11,false,79,249⟩,
⟨.right,38,0,12,false,83,808⟩,
⟨.right,38,0,13,false,77,184⟩,
⟨.right,38,0,14,false,80,1059⟩,
⟨.right,38,0,15,false,81,253⟩,
⟨.right,39,0,(-1),false,385,755⟩,
⟨.right,39,1,(-1),false,384,755⟩,
⟨.right,39,2,(-1),false,386,755⟩,
⟨.right,40,0,(-1),false,321,677⟩,
⟨.right,41,0,(-1),false,36,785⟩,
⟨.right,42,0,(-1),false,387,755⟩,
⟨.right,43,0,(-1),false,322,677⟩,
⟨.right,44,0,(-1),false,170,713⟩,
⟨.right,45,0,(-1),false,12,212⟩,
⟨.right,46,0,(-1),false,233,1115⟩,
⟨.right,47,0,(-1),false,154,1127⟩,
⟨.right,48,0,(-1),false,344,639⟩,
⟨.right,49,0,(-1),false,234,771⟩,
⟨.right,50,0,(-1),false,284,675⟩,
⟨.right,50,1,(-1),false,282,675⟩,
⟨.right,50,2,(-1),false,283,675⟩,
⟨.right,50,3,(-1),false,281,675⟩,
⟨.right,51,0,(-1),false,155,1049⟩,
⟨.right,51,1,0,false,153,1037⟩,
⟨.right,51,1,1,false,141,1008⟩,
⟨.right,51,1,2,false,147,539⟩,
⟨.right,51,1,3,false,149,1000⟩,
⟨.right,52,0,(-1),false,194,717⟩,
⟨.right,52,1,(-1),false,193,99⟩,
⟨.right,53,0,0,false,91,812⟩,
⟨.right,53,0,1,false,85,188⟩,
⟨.right,53,0,2,false,87,1063⟩,
⟨.right,53,0,3,false,89,257⟩,
⟨.right,54,0,(-1),false,385,759⟩,
⟨.right,54,1,(-1),false,384,759⟩,
⟨.right,54,2,(-1),false,386,759⟩,
⟨.right,55,0,(-1),false,321,681⟩,
⟨.right,56,0,(-1),false,36,789⟩,
⟨.right,57,0,(-1),false,387,759⟩,
⟨.right,58,0,(-1),false,322,681⟩,
⟨.right,59,0,(-1),false,170,717⟩,
⟨.right,60,0,(-1),false,12,216⟩,
⟨.right,61,0,(-1),false,233,1112⟩,
⟨.right,62,0,(-1),false,154,1124⟩,
⟨.right,63,0,(-1),false,344,636⟩,
⟨.right,64,0,(-1),false,234,768⟩,
⟨.right,65,0,(-1),false,284,672⟩,
⟨.right,65,1,(-1),false,282,672⟩,
⟨.right,65,2,(-1),false,283,672⟩,
⟨.right,65,3,(-1),false,281,672⟩,
⟨.right,66,0,(-1),false,155,1046⟩,
⟨.right,66,1,0,false,152,1018⟩,
⟨.right,66,1,1,false,140,1018⟩,
⟨.right,66,1,2,false,146,542⟩,
⟨.right,66,1,3,false,148,1018⟩,
⟨.right,66,1,4,false,137,1034⟩,
⟨.right,66,1,5,false,134,792⟩,
⟨.right,66,1,6,false,135,528⟩,
⟨.right,66,1,7,false,136,792⟩,
⟨.right,66,1,8,false,150,320⟩,
⟨.right,66,1,9,false,138,300⟩,
⟨.right,66,1,10,false,142,532⟩,
⟨.right,66,1,11,false,143,308⟩,
⟨.right,66,1,12,false,151,1034⟩,
⟨.right,66,1,13,false,139,801⟩,
⟨.right,66,1,14,false,144,536⟩,
⟨.right,66,1,15,false,145,805⟩,
⟨.right,67,0,(-1),false,194,714⟩,
⟨.right,67,1,(-1),false,193,96⟩,
⟨.right,68,0,0,false,90,796⟩,
⟨.right,68,0,1,false,84,181⟩,
⟨.right,68,0,2,false,86,1056⟩,
⟨.right,68,0,3,false,88,250⟩,
⟨.right,68,0,4,false,54,1052⟩,
⟨.right,68,0,5,false,51,191⟩,
⟨.right,68,0,6,false,52,1066⟩,
⟨.right,68,0,7,false,53,260⟩,
⟨.right,68,0,8,false,82,316⟩,
⟨.right,68,0,9,false,76,181⟩,
⟨.right,68,0,10,false,78,1056⟩,
⟨.right,68,0,11,false,79,250⟩,
⟨.right,68,0,12,false,83,809⟩,
⟨.right,68,0,13,false,77,185⟩,
⟨.right,68,0,14,false,80,1060⟩,
⟨.right,68,0,15,false,81,254⟩,
⟨.right,69,0,(-1),false,385,756⟩,
⟨.right,69,1,(-1),false,384,756⟩,
⟨.right,69,2,(-1),false,386,756⟩,
⟨.right,70,0,(-1),false,321,678⟩,
⟨.right,71,0,(-1),false,36,786⟩,
⟨.right,72,0,(-1),false,387,756⟩,
⟨.right,73,0,(-1),false,322,678⟩,
⟨.right,74,0,(-1),false,170,714⟩,
⟨.right,75,0,(-1),false,12,213⟩,
⟨.right,76,0,(-1),false,233,1116⟩,
⟨.right,77,0,(-1),false,154,1128⟩,
⟨.right,78,0,(-1),false,344,640⟩,
⟨.right,79,0,(-1),false,234,772⟩,
⟨.right,80,0,(-1),false,284,676⟩,
⟨.right,80,1,(-1),false,282,676⟩,
⟨.right,80,2,(-1),false,283,676⟩,
⟨.right,80,3,(-1),false,281,676⟩,
⟨.right,81,0,(-1),false,155,1050⟩,
⟨.right,81,1,0,false,153,1038⟩,
⟨.right,81,1,1,false,141,1009⟩,
⟨.right,81,1,2,false,147,540⟩,
⟨.right,81,1,3,false,149,1001⟩,
⟨.right,82,0,(-1),false,194,718⟩,
⟨.right,82,1,(-1),false,193,100⟩,
⟨.right,83,0,0,false,91,813⟩,
⟨.right,83,0,1,false,85,189⟩,
⟨.right,83,0,2,false,87,1064⟩,
⟨.right,83,0,3,false,89,258⟩,
⟨.right,84,0,(-1),false,385,760⟩,
⟨.right,84,1,(-1),false,384,760⟩,
⟨.right,84,2,(-1),false,386,760⟩,
⟨.right,85,0,(-1),false,321,682⟩,
⟨.right,86,0,(-1),false,36,790⟩,
⟨.right,87,0,(-1),false,387,760⟩,
⟨.right,88,0,(-1),false,322,682⟩,
⟨.right,89,0,(-1),false,170,718⟩,
⟨.right,90,0,(-1),false,12,217⟩
] := by rfl
end M7ContinueSep17.CatalogueGeneral

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def recs676 : List LowerHistoryRecord := [⟨.right,82,0,(-1),false,194,718⟩,⟨.right,82,1,(-1),false,193,100⟩]
theorem records676 : lowerHistoryRecordsFor (⟨.right,82,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs676 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 82)) = recs676
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
noncomputable def recs677 : List LowerHistoryRecord := [⟨.right,83,0,0,false,91,813⟩,⟨.right,83,0,1,false,85,189⟩,⟨.right,83,0,2,false,87,1064⟩,⟨.right,83,0,3,false,89,258⟩]
theorem records677 : lowerHistoryRecordsFor (⟨.right,83,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true)],([3,1,3,1,2,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs677 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 83)) = recs677
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
noncomputable def recs678 : List LowerHistoryRecord := [⟨.right,84,0,(-1),false,385,760⟩,⟨.right,84,1,(-1),false,384,760⟩,⟨.right,84,2,(-1),false,386,760⟩]
theorem records678 : lowerHistoryRecordsFor (⟨.right,84,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false)],([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,3⟩ : LowerHistoryPath) = recs678 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 84)) = recs678
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
noncomputable def recs679 : List LowerHistoryRecord := [⟨.right,85,0,(-1),false,321,682⟩]
theorem records679 : lowerHistoryRecordsFor (⟨.right,85,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false)],([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs679 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 85)) = recs679
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
noncomputable def recs680 : List LowerHistoryRecord := [⟨.right,86,0,(-1),false,36,790⟩]
theorem records680 : lowerHistoryRecordsFor (⟨.right,86,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false)],([3,1,3,1,2,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs680 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 86)) = recs680
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman
namespace M7SplitSep17

theorem premise_lookup_chunk3 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200)
    (hd : d.size = 200) (he : e.size = 200) (i : ℕ) (hi : i < 200) :
    (a ++ b ++ c ++ d ++ e ++ f)[400+i]? = c[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e)
    (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d)
    (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c)
    (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_right (xs := a ++ b)
    (by simp only [Array.size_append, ha, hb]; omega)]
  simp only [Array.size_append, ha, hb]
  exact congrArg (fun j => c[j]?) (by omega)

theorem preSize1 : lowerHistoryPremises01.size = 200 := by rfl
theorem preSize2 : lowerHistoryPremises02.size = 200 := by rfl
theorem preSize3 : lowerHistoryPremises03.size = 200 := by rfl
theorem preSize4 : lowerHistoryPremises04.size = 200 := by rfl
theorem preSize5 : lowerHistoryPremises05.size = 200 := by rfl
theorem premise222 : lowerHistoryPremises[221]? = some ([3,7,21,177,260,371,392,399,425,440,627,650,718,751,814,843,856,984,1067,1107,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 221 = 200+21 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 21 (by decide)]
  rfl
theorem premise333 : lowerHistoryPremises[332]? = some ([3,19,21,44,127,156,170,260,371,372,378,422,425,440,518,527,547,599,618,665,735,751,807,820,843,856,942,1014,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 332 = 200+132 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 132 (by decide)]
  rfl
theorem premise334 : lowerHistoryPremises[333]? = some ([3,19,21,44,127,156,260,371,372,378,422,425,440,518,527,547,599,618,665,735,751,807,843,856,942,1007,1014,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 333 = 200+133 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 133 (by decide)]
  rfl
theorem premise335 : lowerHistoryPremises[334]? = some ([3,19,21,44,127,170,260,371,372,378,422,425,440,518,547,618,665,735,751,807,820,843,856,942,993,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 334 = 200+134 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 134 (by decide)]
  rfl
theorem premise336 : lowerHistoryPremises[335]? = some ([3,19,21,44,127,260,371,372,378,422,425,440,518,547,618,665,735,751,807,843,856,942,993,1007,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 335 = 200+135 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 135 (by decide)]
  rfl
theorem premise337 : lowerHistoryPremises[336]? = some ([3,19,21,44,133,168,189,260,371,374,422,425,440,552,582,636,662,665,685,735,751,807,843,856,965,1060,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 336 = 200+136 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 136 (by decide)]
  rfl
theorem premise338 : lowerHistoryPremises[337]? = some ([3,19,21,44,133,168,260,371,374,422,425,440,552,636,665,685,735,751,807,843,856,965,1035,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 337 = 200+137 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 137 (by decide)]
  rfl
theorem premise339 : lowerHistoryPremises[338]? = some ([3,19,21,44,135,260,371,375,380,422,425,440,509,521,583,665,735,751,807,843,856,929,971,1007,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 338 = 200+138 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 138 (by decide)]
  rfl
theorem premise421 : lowerHistoryPremises[420]? = some ([3,21,207,251,260,264,371,404,422,425,440,699,729,735,751,788,793,803,843,856,1065,1131,1143,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 420 = 400+20 by decide]
  rw [premise_lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 20 (by decide)]
  rfl
theorem premise422 : lowerHistoryPremises[421]? = some ([3,21,207,260,264,371,404,422,425,440,699,735,751,788,803,843,856,1065,1126,1131,1153] : List Nat) := by
  unfold lowerHistoryPremises
  rw [show 421 = 400+21 by decide]
  rw [premise_lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 preSize1 preSize2 preSize3 preSize4 preSize5 21 (by decide)]
  rfl
end M7SplitSep17

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
namespace M7ContinueSep17.Finish50.Six
theorem lookup_chunk1 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[0 + i]? = a[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c) (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b) (by simp only [Array.size_append, ha, hb]; omega)]
  rw [Array.getElem?_append_left (xs := a) (by simp only [Array.size_append, ha]; omega)]
  simp only [Nat.zero_add]
theorem lookup_chunk2 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[200 + i]? = b[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c) (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b) (by simp only [Array.size_append, ha, hb]; omega)]
  rw [Array.getElem?_append_right (xs := a) (by simp only [Array.size_append, ha]; omega)]
  simp only [Array.size_append, ha]
  exact congrArg (fun j => b[j]?) (by omega)
theorem lookup_chunk3 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[400 + i]? = c[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c) (by simp only [Array.size_append, ha, hb, hc]; omega)]
  rw [Array.getElem?_append_right (xs := a ++ b) (by simp only [Array.size_append, ha, hb]; omega)]
  simp only [Array.size_append, ha, hb]
  exact congrArg (fun j => c[j]?) (by omega)
theorem lookup_chunk4 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[600 + i]? = d[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  rw [Array.getElem?_append_right (xs := a ++ b ++ c) (by simp only [Array.size_append, ha, hb, hc]; omega)]
  simp only [Array.size_append, ha, hb, hc]
  exact congrArg (fun j => d[j]?) (by omega)
theorem lookup_chunk5 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[800 + i]? = e[i]? := by
  rw [Array.getElem?_append_left (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  rw [Array.getElem?_append_right (xs := a ++ b ++ c ++ d) (by simp only [Array.size_append, ha, hb, hc, hd]; omega)]
  simp only [Array.size_append, ha, hb, hc, hd]
  exact congrArg (fun j => e[j]?) (by omega)
theorem lookup_chunk6 {α : Type} (a b c d e f : Array α)
    (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200) (hd : d.size = 200) (he : e.size = 200)
    (i : Nat) (hi : i < 200) : (a ++ b ++ c ++ d ++ e ++ f)[1000 + i]? = f[i]? := by
  rw [Array.getElem?_append_right (xs := a ++ b ++ c ++ d ++ e) (by simp only [Array.size_append, ha, hb, hc, hd, he]; omega)]
  simp only [Array.size_append, ha, hb, hc, hd, he]
  exact congrArg (fun j => f[j]?) (by omega)
end M7ContinueSep17.Finish50.Six

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
theorem premise36 : lowerHistoryPremises[35]? = some ([2,3,21,43,260,274,371,430,440,833,843,851,856,1176] : List Nat) := by
  have hg : lowerHistoryPremises[35]? = lowerHistoryPremises01[35]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 35 (by decide)
  exact hg.trans (by rfl)
theorem premise85 : lowerHistoryPremises[84]? = some ([2,3,21,260,274,282,291,371,440,837,843,851,856,858,905] : List Nat) := by
  have hg : lowerHistoryPremises[84]? = lowerHistoryPremises01[84]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 84 (by decide)
  exact hg.trans (by rfl)
theorem premise87 : lowerHistoryPremises[86]? = some ([2,3,21,260,274,282,294,371,440,441,837,843,851,856,904] : List Nat) := by
  have hg : lowerHistoryPremises[86]? = lowerHistoryPremises01[86]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 86 (by decide)
  exact hg.trans (by rfl)
theorem premise89 : lowerHistoryPremises[88]? = some ([2,3,21,260,274,282,294,371,440,837,843,851,856,865,903] : List Nat) := by
  have hg : lowerHistoryPremises[88]? = lowerHistoryPremises01[88]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 88 (by decide)
  exact hg.trans (by rfl)
theorem premise91 : lowerHistoryPremises[90]? = some ([2,3,21,260,274,282,371,440,837,843,851,856,858,904,1174] : List Nat) := by
  have hg : lowerHistoryPremises[90]? = lowerHistoryPremises01[90]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 90 (by decide)
  exact hg.trans (by rfl)
theorem premise193 : lowerHistoryPremises[192]? = some ([3,6,13,21,220,260,282,287,371,419,440,769,784,810,811,837,843,852,856,1181] : List Nat) := by
  have hg : lowerHistoryPremises[192]? = lowerHistoryPremises01[192]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 192 (by decide)
  exact hg.trans (by rfl)
theorem premise194 : lowerHistoryPremises[193]? = some ([3,6,13,21,220,260,282,371,419,440,769,784,810,837,843,856,1165] : List Nat) := by
  have hg : lowerHistoryPremises[193]? = lowerHistoryPremises01[193]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 193 (by decide)
  exact hg.trans (by rfl)
theorem premise321 : lowerHistoryPremises[320]? = some ([3,11,21,26,43,195,260,272,371,440,732,774,824,833,843,856] : List Nat) := by
  have hg : lowerHistoryPremises[320]? = lowerHistoryPremises02[120]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 120 (by decide)
  exact hg.trans (by rfl)
theorem premise384 : lowerHistoryPremises[383]? = some ([3,20,21,42,43,175,249,260,371,440,795,806,824,833,843,856,1138,1150] : List Nat) := by
  have hg : lowerHistoryPremises[383]? = lowerHistoryPremises02[183]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 183 (by decide)
  exact hg.trans (by rfl)
theorem premise385 : lowerHistoryPremises[384]? = some ([3,20,21,42,43,175,258,260,371,440,795,806,824,833,843,856,1150] : List Nat) := by
  have hg : lowerHistoryPremises[384]? = lowerHistoryPremises02[184]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 184 (by decide)
  exact hg.trans (by rfl)
theorem premise386 : lowerHistoryPremises[385]? = some ([3,20,21,42,43,175,260,272,371,440,795,806,824,833,843,856] : List Nat) := by
  have hg : lowerHistoryPremises[385]? = lowerHistoryPremises02[185]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 185 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Noninitial20260918.B675_680
theorem witness100_projection : (lowerHistoryWitness 100).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 100).upperBound = lowerHistoryBound 769 ∧ (lowerHistoryWitness 100).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[99]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 769, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 769, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[99]? = lowerHistoryWitnesses01[99]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 99 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness189_projection : (lowerHistoryWitness 189).lowerBound = lowerHistoryBound 291 ∧ (lowerHistoryWitness 189).upperBound = lowerHistoryBound 905 ∧ (lowerHistoryWitness 189).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[188]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 291, lowerHistoryBound 905, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 291, lowerHistoryBound 905, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[188]? = lowerHistoryWitnesses01[188]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 188 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness258_projection : (lowerHistoryWitness 258).lowerBound = lowerHistoryBound 294 ∧ (lowerHistoryWitness 258).upperBound = lowerHistoryBound 903 ∧ (lowerHistoryWitness 258).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[57]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 294, lowerHistoryBound 903, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 294, lowerHistoryBound 903, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[257]? = lowerHistoryWitnesses02[57]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 57 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness682_projection : (lowerHistoryWitness 682).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 682).upperBound = lowerHistoryBound 732 ∧ (lowerHistoryWitness 682).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[81]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 732, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 732, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[681]? = lowerHistoryWitnesses04[81]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 81 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness718_projection : (lowerHistoryWitness 718).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 718).upperBound = lowerHistoryBound 769 ∧ (lowerHistoryWitness 718).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[117]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 769, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 769, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[717]? = lowerHistoryWitnesses04[117]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 117 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness760_projection : (lowerHistoryWitness 760).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 760).upperBound = lowerHistoryBound 795 ∧ (lowerHistoryWitness 760).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[159]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 795, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 795, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[759]? = lowerHistoryWitnesses04[159]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 159 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness790_projection : (lowerHistoryWitness 790).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 790).upperBound = lowerHistoryBound 833 ∧ (lowerHistoryWitness 790).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[189]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 833, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 833, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[789]? = lowerHistoryWitnesses04[189]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 189 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness813_projection : (lowerHistoryWitness 813).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 813).upperBound = lowerHistoryBound 904 ∧ (lowerHistoryWitness 813).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[12]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 904, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 904, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[812]? = lowerHistoryWitnesses05[12]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 12 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1064_projection : (lowerHistoryWitness 1064).lowerBound = lowerHistoryBound 441 ∧ (lowerHistoryWitness 1064).upperBound = lowerHistoryBound 904 ∧ (lowerHistoryWitness 1064).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[63]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 441, lowerHistoryBound 904, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 441, lowerHistoryBound 904, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1063]? = lowerHistoryWitnesses06[63]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 63 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 100 => (287,769)
  | 189 => (291,905)
  | 258 => (294,903)
  | 682 => (440,732)
  | 718 => (440,769)
  | 760 => (440,795)
  | 790 => (440,833)
  | 813 => (440,904)
  | 1064 => (441,904)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 36 => [2,3,21,43,260,274,371,430,440,833,843,851,856,1176]
  | 85 => [2,3,21,260,274,282,291,371,440,837,843,851,856,858,905]
  | 87 => [2,3,21,260,274,282,294,371,440,441,837,843,851,856,904]
  | 89 => [2,3,21,260,274,282,294,371,440,837,843,851,856,865,903]
  | 91 => [2,3,21,260,274,282,371,440,837,843,851,856,858,904,1174]
  | 193 => [3,6,13,21,220,260,282,287,371,419,440,769,784,810,811,837,843,852,856,1181]
  | 194 => [3,6,13,21,220,260,282,371,419,440,769,784,810,837,843,856,1165]
  | 321 => [3,11,21,26,43,195,260,272,371,440,732,774,824,833,843,856]
  | 384 => [3,20,21,42,43,175,249,260,371,440,795,806,824,833,843,856,1138,1150]
  | 385 => [3,20,21,42,43,175,258,260,371,440,795,806,824,833,843,856,1150]
  | 386 => [3,20,21,42,43,175,260,272,371,440,795,806,824,833,843,856]
  | _ => []
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def src676 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,220],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,220]]
theorem sourceIDs676 : lowerHistorySourcePremises path676 = src676.map (List.map lowerHistoryBound) := by
  have hb : src676.map (List.map lowerHistoryBound) = expected676 := by
    simp only [src676, expected676, List.map_cons, List.map_nil, bound3, bound6, bound13, bound21, bound220, bound260, bound282, bound287, bound371, bound419, bound440, bound769, bound784, bound810, bound811, bound837, bound843, bound852, bound856, bound1165, bound1181]
  exact source676.trans hb.symm
theorem length676 : path676.alternatives = (lowerHistorySourcePremises path676).length := by
  rw [sourceIDs676]
  rfl
theorem binding676 : lowerHistoryPathBinding path676 := by
  apply BindingIds19.pathBinding_from_ids path676 src676 [] recs676 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs676 rfl records676 rfl
  · intro r hr _
    simp only [recs676, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise194)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise193)
  · intro r hr _
    simp only [recs676, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path676] using witness718_projection
    · simpa only [blockWids, path676] using witness100_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path676 recs676 records676 length676 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def path677 : LowerHistoryPath := ⟨.right,83,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true)],([3,1,3,1,2,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩
noncomputable def raw677 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv851,bv2,bv274,bv851]]
noncomputable def expected677 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv851,bv2,bv274]]
theorem structural677 (ops : RootOps19.SourceOps) (b2 b3 b21 b260 b274 b282 b371 b440 b837 b843 b851 b856 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h115 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h116 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h84 : ops.normalization ([2,1],[3]) true false = b282)
    (h129 : ops.necessary ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h38 : ops.normalization ([2,1],[3,1]) false false = b851)
    (h133 : ops.necessary ⟨⟨([3,1,3,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1],[3,1]) = some [b2])
    (h40 : ops.pull (lowerHistoryH7) ([2,1],[3,1]) false = b274)
    (h41 : ops.pull (lowerHistoryHN) ([2,1],[3,1]) false = b851)
    : RootOps19.eval ops path677 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b851,b2,b274,b851]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path677, h0, h115, h2, h116, h84, h129, h38, h133, h40, h41, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource677 : lowerHistorySourcePremises path677 = raw677.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural677 RootOps19.actualOps bv2 bv3 bv21 bv260 bv274 bv282 bv371 bv440 bv837 bv843 bv851 bv856 op0 op115 op2 op116 op84 op129 op38 op133 op40 op41
theorem dedup677 : raw677.map List.eraseDups = expected677 := by
  decide +kernel
theorem source677 : lowerHistorySourcePremises path677 = expected677 := (rawSource677).trans (dedup677)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def extraIDs677 : List (List Nat) := [[858,1174,904],[858,291,905],[294,441,904],[294,865,903]]
noncomputable def extraExpected677 : List (List CertBound) := [[bv858,bv1174,bv904],[bv858,bv291,bv905],[bv294,bv441,bv904],[bv294,bv865,bv903]]
theorem extraValues677 : (List.range 4).map (BindingIds19.extras path677) = extraExpected677 := by
  decide +kernel
theorem extraIDs_sound677 : (List.range extraIDs677.length).map (BindingIds19.extras path677) = extraIDs677.map (List.map lowerHistoryBound) := by
  have hb : extraIDs677.map (List.map lowerHistoryBound) = extraExpected677 := by
    simp only [extraIDs677, extraExpected677, List.map_cons, List.map_nil, bound291, bound294, bound441, bound858, bound865, bound903, bound904, bound905, bound1174]
  exact extraValues677.trans hb.symm
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def src677 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,851,2,274]]
theorem sourceIDs677 : lowerHistorySourcePremises path677 = src677.map (List.map lowerHistoryBound) := by
  have hb : src677.map (List.map lowerHistoryBound) = expected677 := by
    simp only [src677, expected677, List.map_cons, List.map_nil, bound2, bound3, bound21, bound260, bound274, bound282, bound371, bound440, bound837, bound843, bound851, bound856]
  exact source677.trans hb.symm
theorem length677 : path677.alternatives = (lowerHistorySourcePremises path677).length := by
  rw [sourceIDs677]
  rfl
theorem binding677 : lowerHistoryPathBinding path677 := by
  apply BindingIds19.pathBinding_from_ids path677 src677 extraIDs677 recs677 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs677 extraIDs_sound677 records677 rfl
  · intro r hr _
    simp only [recs677, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise91)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise85)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise87)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise89)
  · intro r hr _
    simp only [recs677, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path677] using witness813_projection
    · simpa only [blockWids, path677] using witness189_projection
    · simpa only [blockWids, path677] using witness1064_projection
    · simpa only [blockWids, path677] using witness258_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path677 recs677 records677 length677 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
open BindingNumeric20
theorem op134 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [bv43] := by
  decide +kernel
theorem op6 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) false = bv824 := by
  norm_num [bv824, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op7 : lowerHistoryPull (lowerHistoryH5) ([2,1],[3]) false = bv1150 := by
  norm_num [bv1150, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op97 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH6)) ([2,1],[3]) false = bv258 := by
  norm_num [bv258, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op8 : lowerHistoryPull (lowerHistoryH6) ([2,1],[3]) false = bv1138 := by
  norm_num [bv1138, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op98 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7Mixed)) ([2,1],[3]) false = bv249 := by
  norm_num [bv249, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op99 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) false = bv272 := by
  norm_num [bv272, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op12 : lowerHistoryNormalization ([2,1,3],[3,1]) false false = bv806 := by
  norm_num [bv806, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op135 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,1,3],[3,1]) = some [bv20] := by
  decide +kernel
theorem op14 : lowerHistoryNormalization ([2,1,3,1],[3,1]) false false = bv795 := by
  norm_num [bv795, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op136 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,3,1],[3,1]) = some [bv42] := by
  decide +kernel
theorem op16 : lowerHistoryPull (lowerHistoryH7) ([2,1,3,1],[3,1]) false = bv175 := by
  norm_num [bv175, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
open BindingNumeric20
theorem op17 : lowerHistoryPull (lowerHistoryHN) ([2,1,3,1],[3,1]) false = bv795 := by
  norm_num [bv795, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op20 : lowerHistoryNormalization ([2,1,2],[3,1]) false false = bv774 := by
  norm_num [bv774, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op137 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [bv11] := by
  decide +kernel
theorem op22 : lowerHistoryNormalization ([2,1,2,1],[3,1]) false false = bv732 := by
  norm_num [bv732, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op138 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,2,1],[3,1]) = some [bv26] := by
  decide +kernel
theorem op24 : lowerHistoryPull (lowerHistoryH7) ([2,1,2,1],[3,1]) false = bv195 := by
  norm_num [bv195, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op25 : lowerHistoryPull (lowerHistoryHN) ([2,1,2,1],[3,1]) false = bv732 := by
  norm_num [bv732, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op104 : lowerHistoryPull (lowerHistoryH2) ([2,1],[3]) false = bv430 := by
  norm_num [bv430, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op105 : lowerHistoryNormalization ([2,1],[3,1]) false true = bv1176 := by
  norm_num [bv1176, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op139 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([],[1]),false)⟩ ([2,1],[3,1]) = some [bv2] := by
  decide +kernel
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def path678 : LowerHistoryPath := ⟨.right,84,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false)],([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,3⟩
noncomputable def raw678 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv1150,bv258,bv806,bv20,bv795,bv42,bv175,bv795],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv1150,bv1138,bv249,bv806,bv20,bv795,bv42,bv175,bv795],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv272,bv806,bv20,bv795,bv42,bv175,bv795]]
noncomputable def expected678 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv1150,bv258,bv806,bv20,bv795,bv42,bv175],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv1150,bv1138,bv249,bv806,bv20,bv795,bv42,bv175],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv272,bv806,bv20,bv795,bv42,bv175]]
theorem structural678 (ops : RootOps19.SourceOps) (b3 b20 b21 b42 b43 b175 b249 b258 b260 b272 b371 b440 b795 b806 b824 b833 b843 b856 b1138 b1150 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h115 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h116 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h4 : ops.normalization ([2,1],[3]) false false = b833)
    (h134 : ops.necessary ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) false = b824)
    (h7 : ops.pull (lowerHistoryH5) ([2,1],[3]) false = b1150)
    (h97 : ops.pull ((lowerHistoryComplement lowerHistoryH6)) ([2,1],[3]) false = b258)
    (h8 : ops.pull (lowerHistoryH6) ([2,1],[3]) false = b1138)
    (h98 : ops.pull ((lowerHistoryComplement lowerHistoryH7Mixed)) ([2,1],[3]) false = b249)
    (h99 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) false = b272)
    (h12 : ops.normalization ([2,1,3],[3,1]) false false = b806)
    (h135 : ops.necessary ⟨⟨([3,1,3,1,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,1,3],[3,1]) = some [b20])
    (h14 : ops.normalization ([2,1,3,1],[3,1]) false false = b795)
    (h136 : ops.necessary ⟨⟨([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,3,1],[3,1]) = some [b42])
    (h16 : ops.pull (lowerHistoryH7) ([2,1,3,1],[3,1]) false = b175)
    (h17 : ops.pull (lowerHistoryHN) ([2,1,3,1],[3,1]) false = b795)
    : RootOps19.eval ops path678 = ([[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b258,b806,b20,b795,b42,b175,b795],[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b249,b806,b20,b795,b42,b175,b795],[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b806,b20,b795,b42,b175,b795]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path678, h0, h115, h2, h116, h4, h134, h6, h7, h97, h8, h98, h99, h12, h135, h14, h136, h16, h17, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource678 : lowerHistorySourcePremises path678 = raw678.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural678 RootOps19.actualOps bv3 bv20 bv21 bv42 bv43 bv175 bv249 bv258 bv260 bv272 bv371 bv440 bv795 bv806 bv824 bv833 bv843 bv856 bv1138 bv1150 op0 op115 op2 op116 op4 op134 op6 op7 op97 op8 op98 op99 op12 op135 op14 op136 op16 op17
theorem dedup678 : raw678.map List.eraseDups = expected678 := by
  decide +kernel
theorem source678 : lowerHistorySourcePremises path678 = expected678 := (rawSource678).trans (dedup678)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def src678 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,1150,258,806,20,795,42,175],[371,843,260,440,3,856,21,833,43,824,1150,1138,249,806,20,795,42,175],[371,843,260,440,3,856,21,833,43,824,272,806,20,795,42,175]]
theorem sourceIDs678 : lowerHistorySourcePremises path678 = src678.map (List.map lowerHistoryBound) := by
  have hb : src678.map (List.map lowerHistoryBound) = expected678 := by
    simp only [src678, expected678, List.map_cons, List.map_nil, bound3, bound20, bound21, bound42, bound43, bound175, bound249, bound258, bound260, bound272, bound371, bound440, bound795, bound806, bound824, bound833, bound843, bound856, bound1138, bound1150]
  exact source678.trans hb.symm
theorem length678 : path678.alternatives = (lowerHistorySourcePremises path678).length := by
  rw [sourceIDs678]
  rfl
theorem binding678 : lowerHistoryPathBinding path678 := by
  apply BindingIds19.pathBinding_from_ids path678 src678 [] recs678 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs678 rfl records678 rfl
  · intro r hr _
    simp only [recs678, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise385)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise384)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise386)
  · intro r hr _
    simp only [recs678, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockWids, path678] using witness760_projection
    · simpa only [blockWids, path678] using witness760_projection
    · simpa only [blockWids, path678] using witness760_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path678 recs678 records678 length678 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def path679 : LowerHistoryPath := ⟨.right,85,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false)],([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩
noncomputable def raw679 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv272,bv774,bv11,bv732,bv26,bv195,bv732]]
noncomputable def expected679 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv272,bv774,bv11,bv732,bv26,bv195]]
theorem structural679 (ops : RootOps19.SourceOps) (b3 b11 b21 b26 b43 b195 b260 b272 b371 b440 b732 b774 b824 b833 b843 b856 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h115 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h116 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h4 : ops.normalization ([2,1],[3]) false false = b833)
    (h134 : ops.necessary ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) false = b824)
    (h99 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) false = b272)
    (h20 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (h137 : ops.necessary ⟨⟨([3,1,3,1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [b11])
    (h22 : ops.normalization ([2,1,2,1],[3,1]) false false = b732)
    (h138 : ops.necessary ⟨⟨([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,2,1],[3,1]) = some [b26])
    (h24 : ops.pull (lowerHistoryH7) ([2,1,2,1],[3,1]) false = b195)
    (h25 : ops.pull (lowerHistoryHN) ([2,1,2,1],[3,1]) false = b732)
    : RootOps19.eval ops path679 = ([[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b732]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[1]) = [[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path679, h0, h115, h2, h116, h4, h134, h6, h99, h20, h137, h22, h138, h24, h25, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource679 : lowerHistorySourcePremises path679 = raw679.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural679 RootOps19.actualOps bv3 bv11 bv21 bv26 bv43 bv195 bv260 bv272 bv371 bv440 bv732 bv774 bv824 bv833 bv843 bv856 op0 op115 op2 op116 op4 op134 op6 op99 op20 op137 op22 op138 op24 op25
theorem dedup679 : raw679.map List.eraseDups = expected679 := by
  decide +kernel
theorem source679 : lowerHistorySourcePremises path679 = expected679 := (rawSource679).trans (dedup679)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def src679 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,195]]
theorem sourceIDs679 : lowerHistorySourcePremises path679 = src679.map (List.map lowerHistoryBound) := by
  have hb : src679.map (List.map lowerHistoryBound) = expected679 := by
    simp only [src679, expected679, List.map_cons, List.map_nil, bound3, bound11, bound21, bound26, bound43, bound195, bound260, bound272, bound371, bound440, bound732, bound774, bound824, bound833, bound843, bound856]
  exact source679.trans hb.symm
theorem length679 : path679.alternatives = (lowerHistorySourcePremises path679).length := by
  rw [sourceIDs679]
  rfl
theorem binding679 : lowerHistoryPathBinding path679 := by
  apply BindingIds19.pathBinding_from_ids path679 src679 [] recs679 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs679 rfl records679 rfl
  · intro r hr _
    simp only [recs679, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise321)
  · intro r hr _
    simp only [recs679, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path679] using witness682_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path679 recs679 records679 length679 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def path680 : LowerHistoryPath := ⟨.right,86,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false)],([3,1,3,1,2,1],[3,1,3,1]),(false,false),false,2,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩
noncomputable def raw680 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv430,bv1176,bv2,bv274,bv851]]
noncomputable def expected680 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv430,bv1176,bv2,bv274,bv851]]
theorem structural680 (ops : RootOps19.SourceOps) (b2 b3 b21 b43 b260 b274 b371 b430 b440 b833 b843 b851 b856 b1176 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h115 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h116 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h4 : ops.normalization ([2,1],[3]) false false = b833)
    (h134 : ops.necessary ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (h104 : ops.pull (lowerHistoryH2) ([2,1],[3]) false = b430)
    (h105 : ops.normalization ([2,1],[3,1]) false true = b1176)
    (h139 : ops.necessary ⟨⟨([3,1,3,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([],[1]),false)⟩ ([2,1],[3,1]) = some [b2])
    (h40 : ops.pull (lowerHistoryH7) ([2,1],[3,1]) false = b274)
    (h41 : ops.pull (lowerHistoryHN) ([2,1],[3,1]) false = b851)
    : RootOps19.eval ops path680 = ([[b371,b843,b260,b440,b3,b856,b21,b833,b43,b430,b1176,b2,b274,b851]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path680, h0, h115, h2, h116, h4, h134, h104, h105, h139, h40, h41, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource680 : lowerHistorySourcePremises path680 = raw680.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural680 RootOps19.actualOps bv2 bv3 bv21 bv43 bv260 bv274 bv371 bv430 bv440 bv833 bv843 bv851 bv856 bv1176 op0 op115 op2 op116 op4 op134 op104 op105 op139 op40 op41
theorem dedup680 : raw680.map List.eraseDups = expected680 := by
  decide +kernel
theorem source680 : lowerHistorySourcePremises path680 = expected680 := (rawSource680).trans (dedup680)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
noncomputable def src680 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,430,1176,2,274,851]]
theorem sourceIDs680 : lowerHistorySourcePremises path680 = src680.map (List.map lowerHistoryBound) := by
  have hb : src680.map (List.map lowerHistoryBound) = expected680 := by
    simp only [src680, expected680, List.map_cons, List.map_nil, bound2, bound3, bound21, bound43, bound260, bound274, bound371, bound430, bound440, bound833, bound843, bound851, bound856, bound1176]
  exact source680.trans hb.symm
theorem length680 : path680.alternatives = (lowerHistorySourcePremises path680).length := by
  rw [sourceIDs680]
  rfl
theorem binding680 : lowerHistoryPathBinding path680 := by
  apply BindingIds19.pathBinding_from_ids path680 src680 [] recs680 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs680 rfl records680 rfl
  · intro r hr _
    simp only [recs680, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise36)
  · intro r hr _
    simp only [recs680, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path680] using witness790_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path680 recs680 records680 length680 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B675_680

set_option Elab.async false
set_option maxRecDepth 30000
open Freiman
namespace M7ContinueSep17.CatalogueGeneral
theorem pathSizeL : lowerHistoryPathsL.size = 594 := by rfl
theorem pathSizeR : lowerHistoryPathsR.size = 90 := by rfl
theorem pathSizeM : lowerHistoryPathsM.size = 312 := by rfl
theorem pathSizeX : lowerHistoryPathsX.size = 90 := by rfl
theorem pathSizeH : lowerHistoryPathsH.size = 406 := by rfl
theorem pathLookupL (i : Nat) (hi : i < 594) : lowerHistoryPaths[0+i]? = lowerHistoryPathsL[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Nat.zero_add]
theorem pathLookupR (i : Nat) (hi : i < 90) : lowerHistoryPaths[594+i]? = lowerHistoryPathsR[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryPathsL) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]
  exact congrArg (fun j => lowerHistoryPathsR[j]?) (by omega)
theorem pathLookupM (i : Nat) (hi : i < 312) : lowerHistoryPaths[684+i]? = lowerHistoryPathsM[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryPathsL ++ lowerHistoryPathsR) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]
  exact congrArg (fun j => lowerHistoryPathsM[j]?) (by omega)
theorem pathLookupX (i : Nat) (hi : i < 90) : lowerHistoryPaths[996+i]? = lowerHistoryPathsX[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_left (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]
  exact congrArg (fun j => lowerHistoryPathsX[j]?) (by omega)
theorem pathLookupH (i : Nat) (hi : i < 406) : lowerHistoryPaths[1086+i]? = lowerHistoryPathsH[i]? := by
  unfold lowerHistoryPaths
  rw [Array.getElem?_append_right (xs := lowerHistoryPathsL ++ lowerHistoryPathsR ++ lowerHistoryPathsM ++ lowerHistoryPathsX) (by simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]; omega)]
  simp only [Array.size_append, pathSizeL, pathSizeR, pathSizeM, pathSizeX, pathSizeH]
  exact congrArg (fun j => lowerHistoryPathsH[j]?) (by omega)
end M7ContinueSep17.CatalogueGeneral

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B675_680
theorem _root_.solution : lowerHistoryBindingBatch 675 680 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[675]? = some M7ContinueSep17.Noninitial20260918.B675_680.path676 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 81 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding676
  · have hl : lowerHistoryPaths[676]? = some M7ContinueSep17.Noninitial20260918.B675_680.path677 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 82 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding677
  · have hl : lowerHistoryPaths[677]? = some M7ContinueSep17.Noninitial20260918.B675_680.path678 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 83 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding678
  · have hl : lowerHistoryPaths[678]? = some M7ContinueSep17.Noninitial20260918.B675_680.path679 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 84 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding679
  · have hl : lowerHistoryPaths[679]? = some M7ContinueSep17.Noninitial20260918.B675_680.path680 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 85 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding680
end M7ContinueSep17.Noninitial20260918.B675_680

#print axioms solution
