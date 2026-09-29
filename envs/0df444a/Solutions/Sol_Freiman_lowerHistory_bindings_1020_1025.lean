-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1020_1025
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T04:06:21.738313+00:00
-- url     : https://prove2.me/submissions/dc5c1b9c-9d9d-4b1a-921d-808b9dc89918

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
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def bv2 : CertBound := ⟨true,false,⟨⟨(-605239/322621),(452861/322621),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩⟩⟩
noncomputable def bv6 : CertBound := ⟨true,false,⟨⟨(-2396241/3388429),(1794784/3388429),(0),(0)⟩,⟨(247/649),(1/649),(0),(0)⟩,⟨(177/454),(-1/454),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv11 : CertBound := ⟨true,false,⟨⟨(-5111577/15657181),(3840568/15657181),(0),(0)⟩,⟨(483/1318),(1/1318),(0),(0)⟩,⟨(383/1033),(-1/1033),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv20 : CertBound := ⟨true,false,⟨⟨(-8845164/47149609),(6653521/47149609),(0),(0)⟩,⟨(797/2221),(1/2221),(0),(0)⟩,⟨(667/1846),(-1/1846),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩⟩⟩
noncomputable def bv43 : CertBound := ⟨true,false,⟨⟨(-27041/364702),(168601/1094106),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩⟩⟩
noncomputable def bv235 : CertBound := ⟨true,false,⟨⟨(283141369701/2590896074000),(7255179891/2590896074000),(0),(0)⟩,⟨(9467/26234),(1/78702),(0),(0)⟩,⟨(667/1846),(-1/1846),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩⟩⟩
noncomputable def bv246 : CertBound := ⟨true,false,⟨⟨(12740018571/65624465320),(6136962399/1640611633000),(0),(0)⟩,⟨(5491/14843),(1/44529),(0),(0)⟩,⟨(383/1033),(-1/1033),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩⟩⟩
noncomputable def bv254 : CertBound := ⟨true,false,⟨⟨(11/47),(0),(0),(4/329)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv260 : CertBound := ⟨true,false,⟨⟨(31/100),(0),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv269 : CertBound := ⟨true,false,⟨⟨(70757924607/162104786000),(455373477/162104786000),(0),(0)⟩,⟨(2589/6674),(1/20022),(0),(0)⟩,⟨(177/454),(-1/454),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩⟩⟩
noncomputable def bv272 : CertBound := ⟨true,false,⟨⟨(33285470319/67820291500),(-327225429/33910145750),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(2747/7501),(-1/7501),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv415 : CertBound := ⟨true,true,⟨⟨(43/370),(0),(0),(11/2590)⟩,⟨(3/10),(0),(0),(1/70)⟩,⟨(29/74),(0),(0),(-1/222)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv421 : CertBound := ⟨true,true,⟨⟨(5/17),(0),(0),(-4/85)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(63/170),(0),(0),(-1/510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv430 : CertBound := ⟨true,true,⟨⟨(3418287291/5478244850),(-26216794/8217367275),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),(0),(0)⟩,⟨(-1/2),(1/2),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv692 : CertBound := ⟨false,false,⟨⟨(619410/10727197),(1569896/10727197),(0),(0)⟩,⟨(93/262),(1/262),(0),(0)⟩,⟨(4519/12598),(-1/12598),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv726 : CertBound := ⟨false,false,⟨⟨(2953/30251),(8625/30251),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(66/179),(-1/537),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv762 : CertBound := ⟨false,false,⟨⟨(134271064789/800620860650),(684814167/1601241721300),(0),(0)⟩,⟨(797/2221),(1/2221),(0),(0)⟩,⟨(667/1846),(-1/1846),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv774 : CertBound := ⟨false,false,⟨⟨(41/185),(0),(0),(32/1295)⟩,⟨(3/10),(0),(0),(1/70)⟩,⟨(29/74),(0),(0),(-1/222)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv784 : CertBound := ⟨false,false,⟨⟨(13766/50713),(29019/50713),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv789 : CertBound := ⟨false,false,⟨⟨(154748703689/531731481700),(100050183/265865740850),(0),(0)⟩,⟨(483/1318),(1/1318),(0),(0)⟩,⟨(383/1033),(-1/1033),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv806 : CertBound := ⟨false,false,⟨⟨(13/34),(0),(0),(-7/170)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(63/170),(0),(0),(-1/510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv810 : CertBound := ⟨false,false,⟨⟨(43/94),(0),(0),(37/658)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv824 : CertBound := ⟨false,false,⟨⟨(3418287291/5478244850),(-26216794/8217367275),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv825 : CertBound := ⟨false,false,⟨⟨(71989848497/115073995300),(-76209381/57536997650),(0),(0)⟩,⟨(247/649),(1/649),(0),(0)⟩,⟨(177/454),(-1/454),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv833 : CertBound := ⟨false,false,⟨⟨(7/10),(0),(0),(1/70)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv856 : CertBound := ⟨false,false,⟨⟨(3/2),(0),(0),(1/10)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv1124 : CertBound := ⟨false,true,⟨⟨(17288019/81914300),(23104949/409571500),(0),(0)⟩,⟨(93/262),(1/262),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1138 : CertBound := ⟨false,true,⟨⟨(12374850333/44281430000),(0),(0),(547966053/44281430000)⟩,⟨(1859/5158),(0),(0),(1/5158)⟩,⟨(63/170),(0),(0),(-1/510)⟩,⟨(725/2602),(0),(0),(1/2602)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv1150 : CertBound := ⟨false,true,⟨⟨(33285470319/67820291500),(-327225429/33910145750),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(2747/7501),(-1/7501),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1176 : CertBound := ⟨false,true,⟨⟨(13/10),(0),(0),(9/70)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [bv371,bv843,bv260,bv440] := by
  simpa only [bv371,bv843,bv260,bv440] using BindingNumeric20.initial_base
theorem op78 : lowerHistoryRelaxedGoodness ⟨([2],[3,1]),(false,false)⟩ = some [bv3] := by
  decide +kernel
theorem op2 : lowerHistoryNormalization ([2],[3]) false false = bv856 := by
  norm_num [bv856, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op79 : lowerHistoryNecessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [bv21] := by
  decide +kernel
theorem op41 : lowerHistoryNormalization ([2,1],[3]) false false = bv833 := by
  norm_num [bv833, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op106 : lowerHistoryNecessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [bv43] := by
  decide +kernel
theorem op43 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) false = bv824 := by
  norm_num [bv824, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op48 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) false = bv272 := by
  norm_num [bv272, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op54 : lowerHistoryNormalization ([2,1,2],[3,1]) false false = bv774 := by
  norm_num [bv774, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op108 : lowerHistoryNecessary ⟨⟨([2,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [bv11] := by
  decide +kernel
theorem op56 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) false = bv789 := by
  norm_num [bv789, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op57 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,2],[3,1]) false = bv246 := by
  norm_num [bv246, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
open BindingNumeric20
theorem op58 : lowerHistoryPull (lowerHistoryHN) ([2,1,2],[3,1]) false = bv774 := by
  norm_num [bv774, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op59 : lowerHistoryPull (lowerHistoryH2) ([2,1],[3]) false = bv430 := by
  norm_num [bv430, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op60 : lowerHistoryNormalization ([2,1],[3,1]) false true = bv1176 := by
  norm_num [bv1176, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op109 : lowerHistoryNecessary ⟨⟨([2,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([],[1]),false)⟩ ([2,1],[3,1]) = some [bv2] := by
  decide +kernel
theorem op33 : lowerHistoryNormalization ([2,1,1],[3,1]) false false = bv810 := by
  norm_num [bv810, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op105 : lowerHistoryNecessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [bv6] := by
  decide +kernel
theorem op35 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) false = bv825 := by
  norm_num [bv825, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op36 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) false = bv269 := by
  norm_num [bv269, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op37 : lowerHistoryPull (lowerHistoryHN) ([2,1,1],[3,1]) false = bv810 := by
  norm_num [bv810, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op44 : lowerHistoryPull (lowerHistoryH5) ([2,1],[3]) false = bv1150 := by
  norm_num [bv1150, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op46 : lowerHistoryPull (lowerHistoryH6) ([2,1],[3]) false = bv1138 := by
  norm_num [bv1138, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op62 : lowerHistoryPull (lowerHistoryH7Mixed) ([2,1],[3]) false = bv1124 := by
  norm_num [bv1124, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def path1021 : LowerHistoryPath := ⟨.rightMixed,25,[2],([2],[3]),false,[(([1],[]),false),(([2],[1]),false)],([2,2,1,2],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
noncomputable def raw1021 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv272,bv774,bv11,bv789,bv246,bv774]]
noncomputable def expected1021 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv272,bv774,bv11,bv789,bv246]]
theorem structural1021 (ops : RootOps19.SourceOps) (b3 b11 b21 b43 b246 b260 b272 b371 b440 b774 b789 b824 b833 b843 b856 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h78 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h79 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h41 : ops.normalization ([2,1],[3]) false false = b833)
    (h106 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (h43 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) false = b824)
    (h48 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) false = b272)
    (h54 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (h108 : ops.necessary ⟨⟨([2,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [b11])
    (h56 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) false = b789)
    (h57 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,2],[3,1]) false = b246)
    (h58 : ops.pull (lowerHistoryHN) ([2,1,2],[3,1]) false = b774)
    : RootOps19.eval ops path1021 = ([[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b789,b246,b774]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[1]) = [[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1021, h0, h78, h2, h79, h41, h106, h43, h48, h54, h108, h56, h57, h58, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1021 : lowerHistorySourcePremises path1021 = raw1021.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1021 RootOps19.actualOps bv3 bv11 bv21 bv43 bv246 bv260 bv272 bv371 bv440 bv774 bv789 bv824 bv833 bv843 bv856 op0 op78 op2 op79 op41 op106 op43 op48 op54 op108 op56 op57 op58
theorem dedup1021 : raw1021.map List.eraseDups = expected1021 := by
  decide +kernel
theorem source1021 : lowerHistorySourcePremises path1021 = expected1021 := (rawSource1021).trans (dedup1021)
end M7ContinueSep17.Noninitial20260918.B1020_1025

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
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
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
theorem bound20 : lowerHistoryBound 20 = bv20 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[19]? = some bv20 := Eq.refl (some bv20)
  exact (BoundCompact16.global_to_chunk1 19 (by decide)).trans hl
theorem bound21 : lowerHistoryBound 21 = bv21 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[20]? = some bv21 := Eq.refl (some bv21)
  exact (BoundCompact16.global_to_chunk1 20 (by decide)).trans hl
theorem bound43 : lowerHistoryBound 43 = bv43 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[42]? = some bv43 := Eq.refl (some bv43)
  exact (BoundCompact16.global_to_chunk1 42 (by decide)).trans hl
theorem bound235 : lowerHistoryBound 235 = bv235 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[34]? = some bv235 := Eq.refl (some bv235)
  exact (BoundCompact16.global_to_chunk2 34 (by decide)).trans hl
theorem bound246 : lowerHistoryBound 246 = bv246 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[45]? = some bv246 := Eq.refl (some bv246)
  exact (BoundCompact16.global_to_chunk2 45 (by decide)).trans hl
theorem bound254 : lowerHistoryBound 254 = bv254 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[53]? = some bv254 := Eq.refl (some bv254)
  exact (BoundCompact16.global_to_chunk2 53 (by decide)).trans hl
theorem bound260 : lowerHistoryBound 260 = bv260 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[59]? = some bv260 := Eq.refl (some bv260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hl
theorem bound269 : lowerHistoryBound 269 = bv269 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[68]? = some bv269 := Eq.refl (some bv269)
  exact (BoundCompact16.global_to_chunk2 68 (by decide)).trans hl
theorem bound272 : lowerHistoryBound 272 = bv272 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[71]? = some bv272 := Eq.refl (some bv272)
  exact (BoundCompact16.global_to_chunk2 71 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound415 : lowerHistoryBound 415 = bv415 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[14]? = some bv415 := Eq.refl (some bv415)
  exact (BoundCompact16.global_to_chunk3 14 (by decide)).trans hl
theorem bound421 : lowerHistoryBound 421 = bv421 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[20]? = some bv421 := Eq.refl (some bv421)
  exact (BoundCompact16.global_to_chunk3 20 (by decide)).trans hl
theorem bound430 : lowerHistoryBound 430 = bv430 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[29]? = some bv430 := Eq.refl (some bv430)
  exact (BoundCompact16.global_to_chunk3 29 (by decide)).trans hl
theorem bound440 : lowerHistoryBound 440 = bv440 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[39]? = some bv440 := Eq.refl (some bv440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hl
theorem bound692 : lowerHistoryBound 692 = bv692 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[91]? = some bv692 := Eq.refl (some bv692)
  exact (BoundCompact16.global_to_chunk4 91 (by decide)).trans hl
theorem bound726 : lowerHistoryBound 726 = bv726 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[125]? = some bv726 := Eq.refl (some bv726)
  exact (BoundCompact16.global_to_chunk4 125 (by decide)).trans hl
theorem bound762 : lowerHistoryBound 762 = bv762 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[161]? = some bv762 := Eq.refl (some bv762)
  exact (BoundCompact16.global_to_chunk4 161 (by decide)).trans hl
theorem bound774 : lowerHistoryBound 774 = bv774 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[173]? = some bv774 := Eq.refl (some bv774)
  exact (BoundCompact16.global_to_chunk4 173 (by decide)).trans hl
theorem bound784 : lowerHistoryBound 784 = bv784 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[183]? = some bv784 := Eq.refl (some bv784)
  exact (BoundCompact16.global_to_chunk4 183 (by decide)).trans hl
theorem bound789 : lowerHistoryBound 789 = bv789 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[188]? = some bv789 := Eq.refl (some bv789)
  exact (BoundCompact16.global_to_chunk4 188 (by decide)).trans hl
theorem bound806 : lowerHistoryBound 806 = bv806 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[5]? = some bv806 := Eq.refl (some bv806)
  exact (BoundCompact16.global_to_chunk5 5 (by decide)).trans hl
theorem bound810 : lowerHistoryBound 810 = bv810 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[9]? = some bv810 := Eq.refl (some bv810)
  exact (BoundCompact16.global_to_chunk5 9 (by decide)).trans hl
theorem bound824 : lowerHistoryBound 824 = bv824 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[23]? = some bv824 := Eq.refl (some bv824)
  exact (BoundCompact16.global_to_chunk5 23 (by decide)).trans hl
theorem bound825 : lowerHistoryBound 825 = bv825 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[24]? = some bv825 := Eq.refl (some bv825)
  exact (BoundCompact16.global_to_chunk5 24 (by decide)).trans hl
theorem bound833 : lowerHistoryBound 833 = bv833 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[32]? = some bv833 := Eq.refl (some bv833)
  exact (BoundCompact16.global_to_chunk5 32 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound856 : lowerHistoryBound 856 = bv856 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[55]? = some bv856 := Eq.refl (some bv856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hl
theorem bound1124 : lowerHistoryBound 1124 = bv1124 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[123]? = some bv1124 := Eq.refl (some bv1124)
  exact (BoundCompact16.global_to_chunk6 123).trans hl
theorem bound1138 : lowerHistoryBound 1138 = bv1138 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[137]? = some bv1138 := Eq.refl (some bv1138)
  exact (BoundCompact16.global_to_chunk6 137).trans hl
theorem bound1150 : lowerHistoryBound 1150 = bv1150 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[149]? = some bv1150 := Eq.refl (some bv1150)
  exact (BoundCompact16.global_to_chunk6 149).trans hl
theorem bound1176 : lowerHistoryBound 1176 = bv1176 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[175]? = some bv1176 := Eq.refl (some bv1176)
  exact (BoundCompact16.global_to_chunk6 175).trans hl
end M7ContinueSep17.Noninitial20260918.B1020_1025

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
theorem catalogListX : catalogRecords .rightMixed = [
⟨.rightMixed,1,0,(-1),false,211,1090⟩,
⟨.rightMixed,2,0,(-1),false,102,1102⟩,
⟨.rightMixed,3,0,(-1),false,347,710⟩,
⟨.rightMixed,4,0,(-1),false,212,710⟩,
⟨.rightMixed,5,0,(-1),false,300,740⟩,
⟨.rightMixed,5,1,(-1),false,298,740⟩,
⟨.rightMixed,5,2,(-1),false,299,740⟩,
⟨.rightMixed,5,3,(-1),false,297,740⟩,
⟨.rightMixed,6,0,(-1),false,103,740⟩,
⟨.rightMixed,6,1,(-1),false,101,740⟩,
⟨.rightMixed,7,0,(-1),false,206,782⟩,
⟨.rightMixed,7,1,(-1),false,205,104⟩,
⟨.rightMixed,8,0,(-1),false,24,782⟩,
⟨.rightMixed,9,0,(-1),false,397,704⟩,
⟨.rightMixed,9,1,(-1),false,396,704⟩,
⟨.rightMixed,9,2,(-1),false,398,704⟩,
⟨.rightMixed,10,0,(-1),false,331,734⟩,
⟨.rightMixed,11,0,(-1),false,20,782⟩,
⟨.rightMixed,12,0,(-1),false,399,704⟩,
⟨.rightMixed,13,0,(-1),false,332,734⟩,
⟨.rightMixed,14,0,(-1),false,198,782⟩,
⟨.rightMixed,15,0,(-1),false,16,284⟩,
⟨.rightMixed,16,0,(-1),false,211,1089⟩,
⟨.rightMixed,17,0,(-1),false,102,1101⟩,
⟨.rightMixed,18,0,(-1),false,347,709⟩,
⟨.rightMixed,19,0,(-1),false,212,709⟩,
⟨.rightMixed,20,0,(-1),false,300,739⟩,
⟨.rightMixed,20,1,(-1),false,298,739⟩,
⟨.rightMixed,20,2,(-1),false,299,739⟩,
⟨.rightMixed,20,3,(-1),false,297,739⟩,
⟨.rightMixed,21,0,(-1),false,103,739⟩,
⟨.rightMixed,21,1,(-1),false,101,739⟩,
⟨.rightMixed,22,0,(-1),false,206,781⟩,
⟨.rightMixed,22,1,(-1),false,205,103⟩,
⟨.rightMixed,23,0,(-1),false,24,781⟩,
⟨.rightMixed,24,0,(-1),false,397,703⟩,
⟨.rightMixed,24,1,(-1),false,396,703⟩,
⟨.rightMixed,24,2,(-1),false,398,703⟩,
⟨.rightMixed,25,0,(-1),false,331,733⟩,
⟨.rightMixed,26,0,(-1),false,20,781⟩,
⟨.rightMixed,27,0,(-1),false,399,703⟩,
⟨.rightMixed,28,0,(-1),false,332,733⟩,
⟨.rightMixed,29,0,(-1),false,198,781⟩,
⟨.rightMixed,30,0,(-1),false,16,283⟩,
⟨.rightMixed,31,0,(-1),false,211,1087⟩,
⟨.rightMixed,32,0,(-1),false,102,1099⟩,
⟨.rightMixed,33,0,(-1),false,347,707⟩,
⟨.rightMixed,34,0,(-1),false,212,707⟩,
⟨.rightMixed,35,0,(-1),false,300,737⟩,
⟨.rightMixed,35,1,(-1),false,298,737⟩,
⟨.rightMixed,35,2,(-1),false,299,737⟩,
⟨.rightMixed,35,3,(-1),false,297,737⟩,
⟨.rightMixed,36,0,(-1),false,103,737⟩,
⟨.rightMixed,36,1,(-1),false,101,737⟩,
⟨.rightMixed,37,0,(-1),false,206,779⟩,
⟨.rightMixed,37,1,(-1),false,205,101⟩,
⟨.rightMixed,38,0,(-1),false,24,779⟩,
⟨.rightMixed,39,0,(-1),false,397,701⟩,
⟨.rightMixed,39,1,(-1),false,396,701⟩,
⟨.rightMixed,39,2,(-1),false,398,701⟩,
⟨.rightMixed,40,0,(-1),false,331,731⟩,
⟨.rightMixed,41,0,(-1),false,20,779⟩,
⟨.rightMixed,42,0,(-1),false,399,701⟩,
⟨.rightMixed,43,0,(-1),false,332,731⟩,
⟨.rightMixed,44,0,(-1),false,198,779⟩,
⟨.rightMixed,45,0,(-1),false,16,281⟩,
⟨.rightMixed,46,0,(-1),false,211,1091⟩,
⟨.rightMixed,47,0,(-1),false,102,1103⟩,
⟨.rightMixed,48,0,(-1),false,347,711⟩,
⟨.rightMixed,49,0,(-1),false,212,711⟩,
⟨.rightMixed,50,0,(-1),false,300,741⟩,
⟨.rightMixed,50,1,(-1),false,298,741⟩,
⟨.rightMixed,50,2,(-1),false,299,741⟩,
⟨.rightMixed,50,3,(-1),false,297,741⟩,
⟨.rightMixed,51,0,(-1),false,103,741⟩,
⟨.rightMixed,51,1,(-1),false,101,741⟩,
⟨.rightMixed,52,0,(-1),false,206,783⟩,
⟨.rightMixed,52,1,(-1),false,205,105⟩,
⟨.rightMixed,53,0,(-1),false,24,783⟩,
⟨.rightMixed,54,0,(-1),false,397,705⟩,
⟨.rightMixed,54,1,(-1),false,396,705⟩,
⟨.rightMixed,54,2,(-1),false,398,705⟩,
⟨.rightMixed,55,0,(-1),false,331,735⟩,
⟨.rightMixed,56,0,(-1),false,20,783⟩,
⟨.rightMixed,57,0,(-1),false,399,705⟩,
⟨.rightMixed,58,0,(-1),false,332,735⟩,
⟨.rightMixed,59,0,(-1),false,198,783⟩,
⟨.rightMixed,60,0,(-1),false,16,285⟩,
⟨.rightMixed,61,0,(-1),false,211,1088⟩,
⟨.rightMixed,62,0,(-1),false,102,1100⟩,
⟨.rightMixed,63,0,(-1),false,347,708⟩,
⟨.rightMixed,64,0,(-1),false,212,708⟩,
⟨.rightMixed,65,0,(-1),false,300,738⟩,
⟨.rightMixed,65,1,(-1),false,298,738⟩,
⟨.rightMixed,65,2,(-1),false,299,738⟩,
⟨.rightMixed,65,3,(-1),false,297,738⟩,
⟨.rightMixed,66,0,(-1),false,103,738⟩,
⟨.rightMixed,66,1,(-1),false,101,738⟩,
⟨.rightMixed,67,0,(-1),false,206,780⟩,
⟨.rightMixed,67,1,(-1),false,205,102⟩,
⟨.rightMixed,68,0,(-1),false,24,780⟩,
⟨.rightMixed,69,0,(-1),false,397,702⟩,
⟨.rightMixed,69,1,(-1),false,396,702⟩,
⟨.rightMixed,69,2,(-1),false,398,702⟩,
⟨.rightMixed,70,0,(-1),false,331,732⟩,
⟨.rightMixed,71,0,(-1),false,20,780⟩,
⟨.rightMixed,72,0,(-1),false,399,702⟩,
⟨.rightMixed,73,0,(-1),false,332,732⟩,
⟨.rightMixed,74,0,(-1),false,198,780⟩,
⟨.rightMixed,75,0,(-1),false,16,282⟩,
⟨.rightMixed,76,0,(-1),false,211,1092⟩,
⟨.rightMixed,77,0,(-1),false,102,1104⟩,
⟨.rightMixed,78,0,(-1),false,347,712⟩,
⟨.rightMixed,79,0,(-1),false,212,712⟩,
⟨.rightMixed,80,0,(-1),false,300,742⟩,
⟨.rightMixed,80,1,(-1),false,298,742⟩,
⟨.rightMixed,80,2,(-1),false,299,742⟩,
⟨.rightMixed,80,3,(-1),false,297,742⟩,
⟨.rightMixed,81,0,(-1),false,103,742⟩,
⟨.rightMixed,81,1,(-1),false,101,742⟩,
⟨.rightMixed,82,0,(-1),false,206,784⟩,
⟨.rightMixed,82,1,(-1),false,205,106⟩,
⟨.rightMixed,83,0,(-1),false,24,784⟩,
⟨.rightMixed,84,0,(-1),false,397,706⟩,
⟨.rightMixed,84,1,(-1),false,396,706⟩,
⟨.rightMixed,84,2,(-1),false,398,706⟩,
⟨.rightMixed,85,0,(-1),false,331,736⟩,
⟨.rightMixed,86,0,(-1),false,20,784⟩,
⟨.rightMixed,87,0,(-1),false,399,706⟩,
⟨.rightMixed,88,0,(-1),false,332,736⟩,
⟨.rightMixed,89,0,(-1),false,198,784⟩,
⟨.rightMixed,90,0,(-1),false,16,286⟩
] := by rfl
end M7ContinueSep17.CatalogueGeneral

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def recs1021 : List LowerHistoryRecord := [⟨.rightMixed,25,0,(-1),false,331,733⟩]
theorem records1021 : lowerHistoryRecordsFor (⟨.rightMixed,25,[2],([2],[3]),false,[(([1],[]),false),(([2],[1]),false)],([2,2,1,2],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1021 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 25)) = recs1021
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
noncomputable def recs1022 : List LowerHistoryRecord := [⟨.rightMixed,26,0,(-1),false,20,781⟩]
theorem records1022 : lowerHistoryRecordsFor (⟨.rightMixed,26,[2],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false)],([2,2,1,1],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1022 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 26)) = recs1022
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
noncomputable def recs1023 : List LowerHistoryRecord := [⟨.rightMixed,27,0,(-1),false,399,703⟩]
theorem records1023 : lowerHistoryRecordsFor (⟨.rightMixed,27,[2],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true)],([2,2,1,3],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1023 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 27)) = recs1023
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
noncomputable def recs1024 : List LowerHistoryRecord := [⟨.rightMixed,28,0,(-1),false,332,733⟩]
theorem records1024 : lowerHistoryRecordsFor (⟨.rightMixed,28,[2],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true)],([2,2,1,2],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1024 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 28)) = recs1024
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
noncomputable def recs1025 : List LowerHistoryRecord := [⟨.rightMixed,29,0,(-1),false,198,781⟩]
theorem records1025 : lowerHistoryRecordsFor (⟨.rightMixed,29,[2],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true)],([2,2,1,1],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1025 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 29)) = recs1025
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
end M7ContinueSep17.Noninitial20260918.B1020_1025

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
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
theorem premise20 : lowerHistoryPremises[19]? = some ([2,3,6,21,43,260,269,371,430,440,810,825,833,843,856,1176] : List Nat) := by
  have hg : lowerHistoryPremises[19]? = lowerHistoryPremises01[19]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 19 (by decide)
  exact hg.trans (by rfl)
theorem premise198 : lowerHistoryPremises[197]? = some ([3,6,21,43,254,260,269,371,440,784,810,825,833,843,856] : List Nat) := by
  have hg : lowerHistoryPremises[197]? = lowerHistoryPremises01[197]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 197 (by decide)
  exact hg.trans (by rfl)
theorem premise331 : lowerHistoryPremises[330]? = some ([3,11,21,43,246,260,272,371,440,774,789,824,833,843,856] : List Nat) := by
  have hg : lowerHistoryPremises[330]? = lowerHistoryPremises02[130]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 130 (by decide)
  exact hg.trans (by rfl)
theorem premise332 : lowerHistoryPremises[331]? = some ([3,11,21,43,246,260,371,415,440,726,774,789,824,833,843,856,1150] : List Nat) := by
  have hg : lowerHistoryPremises[331]? = lowerHistoryPremises02[131]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 131 (by decide)
  exact hg.trans (by rfl)
theorem premise399 : lowerHistoryPremises[398]? = some ([3,20,21,43,235,260,371,421,440,692,762,806,824,833,843,856,1124,1138,1150] : List Nat) := by
  have hg : lowerHistoryPremises[398]? = lowerHistoryPremises02[198]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 198 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
theorem witness703_projection : (lowerHistoryWitness 703).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 703).upperBound = lowerHistoryBound 762 ∧ (lowerHistoryWitness 703).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[102]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 762, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 762, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[702]? = lowerHistoryWitnesses04[102]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 102 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness733_projection : (lowerHistoryWitness 733).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 733).upperBound = lowerHistoryBound 789 ∧ (lowerHistoryWitness 733).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[132]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 789, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 789, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[732]? = lowerHistoryWitnesses04[132]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 132 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness781_projection : (lowerHistoryWitness 781).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 781).upperBound = lowerHistoryBound 825 ∧ (lowerHistoryWitness 781).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[180]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 825, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 825, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[780]? = lowerHistoryWitnesses04[180]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 180 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 703 => (440,762)
  | 733 => (440,789)
  | 781 => (440,825)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 20 => [2,3,6,21,43,260,269,371,430,440,810,825,833,843,856,1176]
  | 198 => [3,6,21,43,254,260,269,371,440,784,810,825,833,843,856]
  | 331 => [3,11,21,43,246,260,272,371,440,774,789,824,833,843,856]
  | 332 => [3,11,21,43,246,260,371,415,440,726,774,789,824,833,843,856,1150]
  | 399 => [3,20,21,43,235,260,371,421,440,692,762,806,824,833,843,856,1124,1138,1150]
  | _ => []
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def src1021 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,272,774,11,789,246]]
theorem sourceIDs1021 : lowerHistorySourcePremises path1021 = src1021.map (List.map lowerHistoryBound) := by
  have hb : src1021.map (List.map lowerHistoryBound) = expected1021 := by
    simp only [src1021, expected1021, List.map_cons, List.map_nil, bound3, bound11, bound21, bound43, bound246, bound260, bound272, bound371, bound440, bound774, bound789, bound824, bound833, bound843, bound856]
  exact source1021.trans hb.symm
theorem length1021 : path1021.alternatives = (lowerHistorySourcePremises path1021).length := by
  rw [sourceIDs1021]
  rfl
theorem binding1021 : lowerHistoryPathBinding path1021 := by
  apply BindingIds19.pathBinding_from_ids path1021 src1021 [] recs1021 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1021 rfl records1021 rfl
  · intro r hr _
    simp only [recs1021, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise331)
  · intro r hr _
    simp only [recs1021, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1021] using witness733_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1021 recs1021 records1021 length1021 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def path1022 : LowerHistoryPath := ⟨.rightMixed,26,[2],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false)],([2,2,1,1],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
noncomputable def raw1022 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv430,bv1176,bv2,bv810,bv6,bv825,bv269,bv810]]
noncomputable def expected1022 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv430,bv1176,bv2,bv810,bv6,bv825,bv269]]
theorem structural1022 (ops : RootOps19.SourceOps) (b2 b3 b6 b21 b43 b260 b269 b371 b430 b440 b810 b825 b833 b843 b856 b1176 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h78 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h79 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h41 : ops.normalization ([2,1],[3]) false false = b833)
    (h106 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (h59 : ops.pull (lowerHistoryH2) ([2,1],[3]) false = b430)
    (h60 : ops.normalization ([2,1],[3,1]) false true = b1176)
    (h109 : ops.necessary ⟨⟨([2,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([],[1]),false)⟩ ([2,1],[3,1]) = some [b2])
    (h33 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (h105 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [b6])
    (h35 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) false = b825)
    (h36 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) false = b269)
    (h37 : ops.pull (lowerHistoryHN) ([2,1,1],[3,1]) false = b810)
    : RootOps19.eval ops path1022 = ([[b371,b843,b260,b440,b3,b856,b21,b833,b43,b430,b1176,b2,b810,b6,b825,b269,b810]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1022, h0, h78, h2, h79, h41, h106, h59, h60, h109, h33, h105, h35, h36, h37, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1022 : lowerHistorySourcePremises path1022 = raw1022.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1022 RootOps19.actualOps bv2 bv3 bv6 bv21 bv43 bv260 bv269 bv371 bv430 bv440 bv810 bv825 bv833 bv843 bv856 bv1176 op0 op78 op2 op79 op41 op106 op59 op60 op109 op33 op105 op35 op36 op37
theorem dedup1022 : raw1022.map List.eraseDups = expected1022 := by
  decide +kernel
theorem source1022 : lowerHistorySourcePremises path1022 = expected1022 := (rawSource1022).trans (dedup1022)
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def src1022 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,430,1176,2,810,6,825,269]]
theorem sourceIDs1022 : lowerHistorySourcePremises path1022 = src1022.map (List.map lowerHistoryBound) := by
  have hb : src1022.map (List.map lowerHistoryBound) = expected1022 := by
    simp only [src1022, expected1022, List.map_cons, List.map_nil, bound2, bound3, bound6, bound21, bound43, bound260, bound269, bound371, bound430, bound440, bound810, bound825, bound833, bound843, bound856, bound1176]
  exact source1022.trans hb.symm
theorem length1022 : path1022.alternatives = (lowerHistorySourcePremises path1022).length := by
  rw [sourceIDs1022]
  rfl
theorem binding1022 : lowerHistoryPathBinding path1022 := by
  apply BindingIds19.pathBinding_from_ids path1022 src1022 [] recs1022 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1022 rfl records1022 rfl
  · intro r hr _
    simp only [recs1022, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise20)
  · intro r hr _
    simp only [recs1022, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1022] using witness781_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1022 recs1022 records1022 length1022 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
open BindingNumeric20
theorem op63 : lowerHistoryNormalization ([2,1,3],[3]) true true = bv421 := by
  norm_num [bv421, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op110 : lowerHistoryNecessary ⟨⟨([2,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,1,3],[3]) = some [bv692] := by
  decide +kernel
theorem op49 : lowerHistoryNormalization ([2,1,3],[3,1]) false false = bv806 := by
  norm_num [bv806, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op111 : lowerHistoryNecessary ⟨⟨([2,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,3],[3,1]) = some [bv20] := by
  decide +kernel
theorem op51 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,3],[3,1]) false = bv762 := by
  norm_num [bv762, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op52 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,3],[3,1]) false = bv235 := by
  norm_num [bv235, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op53 : lowerHistoryPull (lowerHistoryHN) ([2,1,3],[3,1]) false = bv806 := by
  norm_num [bv806, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op66 : lowerHistoryNormalization ([2,1,2],[3]) true true = bv415 := by
  norm_num [bv415, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op112 : lowerHistoryNecessary ⟨⟨([2,2,1,2],[3,1,3]),(true,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,1,2],[3]) = some [bv726] := by
  decide +kernel
theorem op113 : lowerHistoryNecessary ⟨⟨([2,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,2],[3,1]) = some [bv11] := by
  decide +kernel
theorem op69 : lowerHistoryNormalization ([2,1,1],[3]) true false = bv254 := by
  norm_num [bv254, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op114 : lowerHistoryNecessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1,1],[3]) = some [bv784] := by
  decide +kernel
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def path1023 : LowerHistoryPath := ⟨.rightMixed,27,[2],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true)],([2,2,1,3],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
noncomputable def raw1023 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv1150,bv1138,bv1124,bv421,bv692,bv806,bv20,bv762,bv235,bv806]]
noncomputable def expected1023 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv1150,bv1138,bv1124,bv421,bv692,bv806,bv20,bv762,bv235]]
theorem structural1023 (ops : RootOps19.SourceOps) (b3 b20 b21 b43 b235 b260 b371 b421 b440 b692 b762 b806 b824 b833 b843 b856 b1124 b1138 b1150 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h78 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h79 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h41 : ops.normalization ([2,1],[3]) false false = b833)
    (h106 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (h43 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) false = b824)
    (h44 : ops.pull (lowerHistoryH5) ([2,1],[3]) false = b1150)
    (h46 : ops.pull (lowerHistoryH6) ([2,1],[3]) false = b1138)
    (h62 : ops.pull (lowerHistoryH7Mixed) ([2,1],[3]) false = b1124)
    (h63 : ops.normalization ([2,1,3],[3]) true true = b421)
    (h110 : ops.necessary ⟨⟨([2,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,1,3],[3]) = some [b692])
    (h49 : ops.normalization ([2,1,3],[3,1]) false false = b806)
    (h111 : ops.necessary ⟨⟨([2,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,3],[3,1]) = some [b20])
    (h51 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,3],[3,1]) false = b762)
    (h52 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,3],[3,1]) false = b235)
    (h53 : ops.pull (lowerHistoryHN) ([2,1,3],[3,1]) false = b806)
    : RootOps19.eval ops path1023 = ([[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b762,b235,b806]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,lowerHistoryH7Mixed]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1023, h0, h78, h2, h79, h41, h106, h43, h44, h46, h62, h63, h110, h49, h111, h51, h52, h53, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1023 : lowerHistorySourcePremises path1023 = raw1023.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1023 RootOps19.actualOps bv3 bv20 bv21 bv43 bv235 bv260 bv371 bv421 bv440 bv692 bv762 bv806 bv824 bv833 bv843 bv856 bv1124 bv1138 bv1150 op0 op78 op2 op79 op41 op106 op43 op44 op46 op62 op63 op110 op49 op111 op51 op52 op53
theorem dedup1023 : raw1023.map List.eraseDups = expected1023 := by
  decide +kernel
theorem source1023 : lowerHistorySourcePremises path1023 = expected1023 := (rawSource1023).trans (dedup1023)
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def src1023 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,762,235]]
theorem sourceIDs1023 : lowerHistorySourcePremises path1023 = src1023.map (List.map lowerHistoryBound) := by
  have hb : src1023.map (List.map lowerHistoryBound) = expected1023 := by
    simp only [src1023, expected1023, List.map_cons, List.map_nil, bound3, bound20, bound21, bound43, bound235, bound260, bound371, bound421, bound440, bound692, bound762, bound806, bound824, bound833, bound843, bound856, bound1124, bound1138, bound1150]
  exact source1023.trans hb.symm
theorem length1023 : path1023.alternatives = (lowerHistorySourcePremises path1023).length := by
  rw [sourceIDs1023]
  rfl
theorem binding1023 : lowerHistoryPathBinding path1023 := by
  apply BindingIds19.pathBinding_from_ids path1023 src1023 [] recs1023 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1023 rfl records1023 rfl
  · intro r hr _
    simp only [recs1023, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise399)
  · intro r hr _
    simp only [recs1023, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1023] using witness703_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1023 recs1023 records1023 length1023 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def path1024 : LowerHistoryPath := ⟨.rightMixed,28,[2],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true)],([2,2,1,2],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
noncomputable def raw1024 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv1150,bv415,bv726,bv774,bv11,bv789,bv246,bv774]]
noncomputable def expected1024 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv824,bv1150,bv415,bv726,bv774,bv11,bv789,bv246]]
theorem structural1024 (ops : RootOps19.SourceOps) (b3 b11 b21 b43 b246 b260 b371 b415 b440 b726 b774 b789 b824 b833 b843 b856 b1150 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h78 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h79 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h41 : ops.normalization ([2,1],[3]) false false = b833)
    (h106 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (h43 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) false = b824)
    (h44 : ops.pull (lowerHistoryH5) ([2,1],[3]) false = b1150)
    (h66 : ops.normalization ([2,1,2],[3]) true true = b415)
    (h112 : ops.necessary ⟨⟨([2,2,1,2],[3,1,3]),(true,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,1,2],[3]) = some [b726])
    (h54 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (h113 : ops.necessary ⟨⟨([2,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,2],[3,1]) = some [b11])
    (h56 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) false = b789)
    (h57 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,2],[3,1]) false = b246)
    (h58 : ops.pull (lowerHistoryHN) ([2,1,2],[3,1]) false = b774)
    : RootOps19.eval ops path1024 = ([[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b415,b726,b774,b11,b789,b246,b774]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,2,1,2],[3,1,3]),(true,true)⟩,true,false,some (false,([2],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1024, h0, h78, h2, h79, h41, h106, h43, h44, h66, h112, h54, h113, h56, h57, h58, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1024 : lowerHistorySourcePremises path1024 = raw1024.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1024 RootOps19.actualOps bv3 bv11 bv21 bv43 bv246 bv260 bv371 bv415 bv440 bv726 bv774 bv789 bv824 bv833 bv843 bv856 bv1150 op0 op78 op2 op79 op41 op106 op43 op44 op66 op112 op54 op113 op56 op57 op58
theorem dedup1024 : raw1024.map List.eraseDups = expected1024 := by
  decide +kernel
theorem source1024 : lowerHistorySourcePremises path1024 = expected1024 := (rawSource1024).trans (dedup1024)
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def src1024 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,1150,415,726,774,11,789,246]]
theorem sourceIDs1024 : lowerHistorySourcePremises path1024 = src1024.map (List.map lowerHistoryBound) := by
  have hb : src1024.map (List.map lowerHistoryBound) = expected1024 := by
    simp only [src1024, expected1024, List.map_cons, List.map_nil, bound3, bound11, bound21, bound43, bound246, bound260, bound371, bound415, bound440, bound726, bound774, bound789, bound824, bound833, bound843, bound856, bound1150]
  exact source1024.trans hb.symm
theorem length1024 : path1024.alternatives = (lowerHistorySourcePremises path1024).length := by
  rw [sourceIDs1024]
  rfl
theorem binding1024 : lowerHistoryPathBinding path1024 := by
  apply BindingIds19.pathBinding_from_ids path1024 src1024 [] recs1024 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1024 rfl records1024 rfl
  · intro r hr _
    simp only [recs1024, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise332)
  · intro r hr _
    simp only [recs1024, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1024] using witness733_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1024 recs1024 records1024 length1024 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
open BindingNumeric20
theorem op103 : lowerHistoryNecessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [bv6] := by
  decide +kernel
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def path1025 : LowerHistoryPath := ⟨.rightMixed,29,[2],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true)],([2,2,1,1],[3,1,3,1]),(true,false),false,4,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
noncomputable def raw1025 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv254,bv784,bv810,bv6,bv825,bv269,bv810]]
noncomputable def expected1025 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv833,bv43,bv254,bv784,bv810,bv6,bv825,bv269]]
theorem structural1025 (ops : RootOps19.SourceOps) (b3 b6 b21 b43 b254 b260 b269 b371 b440 b784 b810 b825 b833 b843 b856 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h78 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h79 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h41 : ops.normalization ([2,1],[3]) false false = b833)
    (h106 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (h69 : ops.normalization ([2,1,1],[3]) true false = b254)
    (h114 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1,1],[3]) = some [b784])
    (h33 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (h103 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (h35 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) false = b825)
    (h36 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) false = b269)
    (h37 : ops.pull (lowerHistoryHN) ([2,1,1],[3,1]) false = b810)
    : RootOps19.eval ops path1025 = ([[b371,b843,b260,b440,b3,b856,b21,b833,b43,b254,b784,b810,b6,b825,b269,b810]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (false,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1025, h0, h78, h2, h79, h41, h106, h69, h114, h33, h103, h35, h36, h37, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1025 : lowerHistorySourcePremises path1025 = raw1025.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1025 RootOps19.actualOps bv3 bv6 bv21 bv43 bv254 bv260 bv269 bv371 bv440 bv784 bv810 bv825 bv833 bv843 bv856 op0 op78 op2 op79 op41 op106 op69 op114 op33 op103 op35 op36 op37
theorem dedup1025 : raw1025.map List.eraseDups = expected1025 := by
  decide +kernel
theorem source1025 : lowerHistorySourcePremises path1025 = expected1025 := (rawSource1025).trans (dedup1025)
end M7ContinueSep17.Noninitial20260918.B1020_1025

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
noncomputable def src1025 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,254,784,810,6,825,269]]
theorem sourceIDs1025 : lowerHistorySourcePremises path1025 = src1025.map (List.map lowerHistoryBound) := by
  have hb : src1025.map (List.map lowerHistoryBound) = expected1025 := by
    simp only [src1025, expected1025, List.map_cons, List.map_nil, bound3, bound6, bound21, bound43, bound254, bound260, bound269, bound371, bound440, bound784, bound810, bound825, bound833, bound843, bound856]
  exact source1025.trans hb.symm
theorem length1025 : path1025.alternatives = (lowerHistorySourcePremises path1025).length := by
  rw [sourceIDs1025]
  rfl
theorem binding1025 : lowerHistoryPathBinding path1025 := by
  apply BindingIds19.pathBinding_from_ids path1025 src1025 [] recs1025 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1025 rfl records1025 rfl
  · intro r hr _
    simp only [recs1025, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise198)
  · intro r hr _
    simp only [recs1025, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1025] using witness781_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1025 recs1025 records1025 length1025 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B1020_1025

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
namespace M7ContinueSep17.Noninitial20260918.B1020_1025
theorem _root_.solution : lowerHistoryBindingBatch 1020 1025 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1020]? = some M7ContinueSep17.Noninitial20260918.B1020_1025.path1021 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 24 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1021
  · have hl : lowerHistoryPaths[1021]? = some M7ContinueSep17.Noninitial20260918.B1020_1025.path1022 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 25 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1022
  · have hl : lowerHistoryPaths[1022]? = some M7ContinueSep17.Noninitial20260918.B1020_1025.path1023 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 26 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1023
  · have hl : lowerHistoryPaths[1023]? = some M7ContinueSep17.Noninitial20260918.B1020_1025.path1024 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 27 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1024
  · have hl : lowerHistoryPaths[1024]? = some M7ContinueSep17.Noninitial20260918.B1020_1025.path1025 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 28 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1025
end M7ContinueSep17.Noninitial20260918.B1020_1025

#print axioms solution
