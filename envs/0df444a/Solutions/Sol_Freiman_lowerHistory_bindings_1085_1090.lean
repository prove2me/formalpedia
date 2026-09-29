-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1085_1090
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T05:20:19.915296+00:00
-- url     : https://prove2.me/submissions/27e0dc96-89dd-41f6-aaca-b3f4fd9dfde9

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
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def bv1 : CertBound := ⟨true,false,⟨⟨(-5134/1081),(3851/1081),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩⟩⟩
noncomputable def bv37 : CertBound := ⟨true,false,⟨⟨(-160951/1585298),(123103/1585298),(0),(0)⟩,⟨(185/241),(1/241),(0),(0)⟩,⟨(225/286),(-1/286),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv65 : CertBound := ⟨true,false,⟨⟨(-11/670),(0),(0),(27/4690)⟩,⟨(7/10),(0),(0),(1/70)⟩,⟨(519/670),(0),(0),(-1/670)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv132 : CertBound := ⟨true,false,⟨⟨(133/21164),(324/5291),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv217 : CertBound := ⟨true,false,⟨⟨(809632611/13214548150),(312390999/132145481500),(0),(0)⟩,⟨(185/241),(1/241),(0),(0)⟩,⟨(7903/10249),(-1/10249),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv240 : CertBound := ⟨true,false,⟨⟨(2093/16500),(161/4125),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv241 : CertBound := ⟨true,false,⟨⟨(2086474600/15194033387),(72548900/45582100161),(0),(0)⟩,⟨(1172/1499),(-1/4497),(0),(0)⟩,⟨(1277/1621),(1/1621),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv245 : CertBound := ⟨true,false,⟨⟨(25047/134000),(0),(0),(3243/938000)⟩,⟨(7/10),(0),(0),(1/70)⟩,⟨(519/670),(0),(0),(-1/670)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(119/202),(0),(0),(-1/202)⟩⟩⟩
noncomputable def bv260 : CertBound := ⟨true,false,⟨⟨(31/100),(0),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv261 : CertBound := ⟨true,false,⟨⟨(871317/2766500),(-100161/5533000),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩⟩⟩
noncomputable def bv280 : CertBound := ⟨true,false,⟨⟨(113/166),(0),(0),(-23/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(125/166),(0),(0),(1/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv281 : CertBound := ⟨true,false,⟨⟨(7/10),(0),(0),(-9/70)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(7/10),(0),(0),(1/70)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv293 : CertBound := ⟨true,false,⟨⟨(3/2),(0),(0),(1/10)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv296 : CertBound := ⟨true,false,⟨⟨(930648861/322391000),(11126241/322391000),(0),(0)⟩,⟨(1272/3013),(1/3013),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩⟩⟩
noncomputable def bv327 : CertBound := ⟨true,true,⟨⟨(-11/670),(0),(0),(27/4690)⟩,⟨(7/10),(0),(0),(1/70)⟩,⟨(519/670),(0),(0),(-1/670)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv431 : CertBound := ⟨true,true,⟨⟨(113/166),(0),(0),(-23/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(125/166),(0),(0),(1/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv433 : CertBound := ⟨true,true,⟨⟨(729/1024),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),(0),(0)⟩,⟨(-1/2),(1/2),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv538 : CertBound := ⟨false,false,⟨⟨(23980/2838901),(153536/8516703),(0),(0)⟩,⟨(100/131),(1/393),(0),(0)⟩,⟨(14042/18337),(-1/18337),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv679 : CertBound := ⟨false,false,⟨⟨(13455300/263160271),(-4160400/263160271),(0),(0)⟩,⟨(2473/3229),(1/3229),(0),(0)⟩,⟨(2018/2629),(-1/2629),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv701 : CertBound := ⟨false,false,⟨⟨(15754/231803),(11763/231803),(0),(0)⟩,⟨(225/286),(-1/286),(0),(0)⟩,⟨(1277/1621),(1/1621),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv714 : CertBound := ⟨false,false,⟨⟨(18996/231803),(143896/695409),(0),(0)⟩,⟨(1277/1621),(1/1621),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv727 : CertBound := ⟨false,false,⟨⟨(25003083/251579900),(89651/251579900),(0),(0)⟩,⟨(185/241),(1/241),(0),(0)⟩,⟨(225/286),(-1/286),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩⟩⟩
noncomputable def bv757 : CertBound := ⟨false,false,⟨⟨(8772187000/54124907157),(11533000/1745964747),(0),(0)⟩,⟨(185/241),(1/241),(0),(0)⟩,⟨(1172/1499),(-1/4497),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv777 : CertBound := ⟨false,false,⟨⟨(969900/4043237),(-305200/4043237),(0),(0)⟩,⟨(611/781),(1/781),(0),(0)⟩,⟨(132/167),(-1/501),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv799 : CertBound := ⟨false,false,⟨⟨(371/1100),(-1/220),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv832 : CertBound := ⟨false,false,⟨⟨(7/10),(0),(0),(-9/70)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(7/10),(0),(0),(1/70)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv839 : CertBound := ⟨false,false,⟨⟨(9/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv857 : CertBound := ⟨false,false,⟨⟨(10485/6253),(24757/6253),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv867 : CertBound := ⟨false,false,⟨⟨(3),(0),(0),(2/5)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv871 : CertBound := ⟨false,false,⟨⟨(890072666/211092275),(-5511187/2533107300),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv959 : CertBound := ⟨false,true,⟨⟨(55131/8489041),(107453/25467123),(0),(0)⟩,⟨(2473/3229),(1/3229),(0),(0)⟩,⟨(2018/2629),(-1/2629),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1030 : CertBound := ⟨false,true,⟨⟨(11659/391281),(2533/130427),(0),(0)⟩,⟨(611/781),(1/781),(0),(0)⟩,⟨(132/167),(-1/501),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1032 : CertBound := ⟨false,true,⟨⟨(1112027/36529350),(470281/91323375),(0),(0)⟩,⟨(100/131),(1/393),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1033 : CertBound := ⟨false,true,⟨⟨(1594659483/50089334000),(0),(0),(148807953/50089334000)⟩,⟨(5677/7402),(0),(0),(1/7402)⟩,⟨(519/670),(0),(0),(-1/670)⟩,⟨(107/170),(0),(0),(1/510)⟩,⟨(11/10),(0),(0),(-1/10)⟩⟩⟩
noncomputable def bv1076 : CertBound := ⟨false,true,⟨⟨(809632611/13214548150),(312390999/132145481500),(0),(0)⟩,⟨(185/241),(1/241),(0),(0)⟩,⟨(7903/10249),(-1/10249),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1110 : CertBound := ⟨false,true,⟨⟨(2086474600/15194033387),(72548900/45582100161),(0),(0)⟩,⟨(1172/1499),(-1/4497),(0),(0)⟩,⟨(1277/1621),(1/1621),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1115 : CertBound := ⟨false,true,⟨⟨(25047/134000),(0),(0),(3243/938000)⟩,⟨(7/10),(0),(0),(1/70)⟩,⟨(519/670),(0),(0),(-1/670)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(119/202),(0),(0),(-1/202)⟩⟩⟩
noncomputable def bv1140 : CertBound := ⟨false,true,⟨⟨(871317/2766500),(-100161/5533000),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩⟩⟩
noncomputable def bv1162 : CertBound := ⟨false,true,⟨⟨(225/289),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [bv371,bv843,bv260,bv440] := by
  simpa only [bv371,bv843,bv260,bv440] using BindingNumeric20.initial_base
theorem op108 : lowerHistoryRelaxedGoodness ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [bv3] := by
  decide +kernel
theorem op37 : lowerHistoryNormalization ([2],[3]) true false = bv293 := by
  norm_num [bv293, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op136 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([2],[3]) = some [bv857] := by
  decide +kernel
theorem op39 : lowerHistoryNormalization ([2],[3,1]) false false = bv867 := by
  norm_num [bv867, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op137 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[3,1]) = some [bv1] := by
  decide +kernel
theorem op41 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2],[3,1]) false = bv871 := by
  norm_num [bv871, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op42 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2],[3,1]) false = bv296 := by
  norm_num [bv296, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op43 : lowerHistoryPull (lowerHistoryHN) ([2],[3,1]) false = bv867 := by
  norm_num [bv867, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op138 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [bv371,bv843,bv433,bv1162] := by
  decide +kernel
theorem op139 : ([] : List CertBound) = [] := by
  decide +kernel
theorem op140 : lowerHistoryNormalization ([1],[]) false false = bv839 := by
  norm_num [bv839, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def path1086 : LowerHistoryPath := ⟨.rightMixed,90,[3,1,3,1],([2],[3]),true,[(([1],[]),true)],([3,1,3,1,2],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩
noncomputable def raw1086 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv293,bv857,bv867,bv1,bv871,bv296,bv867]]
noncomputable def expected1086 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv293,bv857,bv867,bv1,bv871,bv296]]
theorem structural1086 (ops : RootOps19.SourceOps) (b1 b3 b260 b293 b296 b371 b440 b843 b857 b867 b871 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h108 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h37 : ops.normalization ([2],[3]) true false = b293)
    (h136 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([2],[3]) = some [b857])
    (h39 : ops.normalization ([2],[3,1]) false false = b867)
    (h137 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[3,1]) = some [b1])
    (h41 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2],[3,1]) false = b871)
    (h42 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2],[3,1]) false = b296)
    (h43 : ops.pull (lowerHistoryHN) ([2],[3,1]) false = b867)
    : RootOps19.eval ops path1086 = ([[b371,b843,b260,b440,b3,b293,b857,b867,b1,b871,b296,b867]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1086, h0, h108, h37, h136, h39, h137, h41, h42, h43, hc0, hf0, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1086 : lowerHistorySourcePremises path1086 = raw1086.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1086 RootOps19.actualOps bv1 bv3 bv260 bv293 bv296 bv371 bv440 bv843 bv857 bv867 bv871 op0 op108 op37 op136 op39 op137 op41 op42 op43
theorem dedup1086 : raw1086.map List.eraseDups = expected1086 := by
  decide +kernel
theorem source1086 : lowerHistorySourcePremises path1086 = expected1086 := (rawSource1086).trans (dedup1086)
end M7ContinueSep17.Initial20260918.B1085_1090

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
namespace M7ContinueSep17.Initial20260918.B1085_1090
theorem bound1 : lowerHistoryBound 1 = bv1 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[0]? = some bv1 := Eq.refl (some bv1)
  exact (BoundCompact16.global_to_chunk1 0 (by decide)).trans hl
theorem bound3 : lowerHistoryBound 3 = bv3 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[2]? = some bv3 := Eq.refl (some bv3)
  exact (BoundCompact16.global_to_chunk1 2 (by decide)).trans hl
theorem bound37 : lowerHistoryBound 37 = bv37 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[36]? = some bv37 := Eq.refl (some bv37)
  exact (BoundCompact16.global_to_chunk1 36 (by decide)).trans hl
theorem bound65 : lowerHistoryBound 65 = bv65 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[64]? = some bv65 := Eq.refl (some bv65)
  exact (BoundCompact16.global_to_chunk1 64 (by decide)).trans hl
theorem bound132 : lowerHistoryBound 132 = bv132 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[131]? = some bv132 := Eq.refl (some bv132)
  exact (BoundCompact16.global_to_chunk1 131 (by decide)).trans hl
theorem bound217 : lowerHistoryBound 217 = bv217 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[16]? = some bv217 := Eq.refl (some bv217)
  exact (BoundCompact16.global_to_chunk2 16 (by decide)).trans hl
theorem bound240 : lowerHistoryBound 240 = bv240 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[39]? = some bv240 := Eq.refl (some bv240)
  exact (BoundCompact16.global_to_chunk2 39 (by decide)).trans hl
theorem bound241 : lowerHistoryBound 241 = bv241 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[40]? = some bv241 := Eq.refl (some bv241)
  exact (BoundCompact16.global_to_chunk2 40 (by decide)).trans hl
theorem bound245 : lowerHistoryBound 245 = bv245 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[44]? = some bv245 := Eq.refl (some bv245)
  exact (BoundCompact16.global_to_chunk2 44 (by decide)).trans hl
theorem bound260 : lowerHistoryBound 260 = bv260 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[59]? = some bv260 := Eq.refl (some bv260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hl
theorem bound261 : lowerHistoryBound 261 = bv261 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[60]? = some bv261 := Eq.refl (some bv261)
  exact (BoundCompact16.global_to_chunk2 60 (by decide)).trans hl
theorem bound280 : lowerHistoryBound 280 = bv280 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[79]? = some bv280 := Eq.refl (some bv280)
  exact (BoundCompact16.global_to_chunk2 79 (by decide)).trans hl
theorem bound281 : lowerHistoryBound 281 = bv281 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[80]? = some bv281 := Eq.refl (some bv281)
  exact (BoundCompact16.global_to_chunk2 80 (by decide)).trans hl
theorem bound293 : lowerHistoryBound 293 = bv293 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[92]? = some bv293 := Eq.refl (some bv293)
  exact (BoundCompact16.global_to_chunk2 92 (by decide)).trans hl
theorem bound296 : lowerHistoryBound 296 = bv296 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[95]? = some bv296 := Eq.refl (some bv296)
  exact (BoundCompact16.global_to_chunk2 95 (by decide)).trans hl
theorem bound327 : lowerHistoryBound 327 = bv327 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[126]? = some bv327 := Eq.refl (some bv327)
  exact (BoundCompact16.global_to_chunk2 126 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound431 : lowerHistoryBound 431 = bv431 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[30]? = some bv431 := Eq.refl (some bv431)
  exact (BoundCompact16.global_to_chunk3 30 (by decide)).trans hl
theorem bound433 : lowerHistoryBound 433 = bv433 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[32]? = some bv433 := Eq.refl (some bv433)
  exact (BoundCompact16.global_to_chunk3 32 (by decide)).trans hl
theorem bound440 : lowerHistoryBound 440 = bv440 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[39]? = some bv440 := Eq.refl (some bv440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hl
theorem bound538 : lowerHistoryBound 538 = bv538 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[137]? = some bv538 := Eq.refl (some bv538)
  exact (BoundCompact16.global_to_chunk3 137 (by decide)).trans hl
theorem bound679 : lowerHistoryBound 679 = bv679 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[78]? = some bv679 := Eq.refl (some bv679)
  exact (BoundCompact16.global_to_chunk4 78 (by decide)).trans hl
theorem bound701 : lowerHistoryBound 701 = bv701 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[100]? = some bv701 := Eq.refl (some bv701)
  exact (BoundCompact16.global_to_chunk4 100 (by decide)).trans hl
theorem bound714 : lowerHistoryBound 714 = bv714 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[113]? = some bv714 := Eq.refl (some bv714)
  exact (BoundCompact16.global_to_chunk4 113 (by decide)).trans hl
theorem bound727 : lowerHistoryBound 727 = bv727 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[126]? = some bv727 := Eq.refl (some bv727)
  exact (BoundCompact16.global_to_chunk4 126 (by decide)).trans hl
theorem bound757 : lowerHistoryBound 757 = bv757 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[156]? = some bv757 := Eq.refl (some bv757)
  exact (BoundCompact16.global_to_chunk4 156 (by decide)).trans hl
theorem bound777 : lowerHistoryBound 777 = bv777 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[176]? = some bv777 := Eq.refl (some bv777)
  exact (BoundCompact16.global_to_chunk4 176 (by decide)).trans hl
theorem bound799 : lowerHistoryBound 799 = bv799 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[198]? = some bv799 := Eq.refl (some bv799)
  exact (BoundCompact16.global_to_chunk4 198 (by decide)).trans hl
theorem bound832 : lowerHistoryBound 832 = bv832 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[31]? = some bv832 := Eq.refl (some bv832)
  exact (BoundCompact16.global_to_chunk5 31 (by decide)).trans hl
theorem bound839 : lowerHistoryBound 839 = bv839 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[38]? = some bv839 := Eq.refl (some bv839)
  exact (BoundCompact16.global_to_chunk5 38 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound857 : lowerHistoryBound 857 = bv857 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[56]? = some bv857 := Eq.refl (some bv857)
  exact (BoundCompact16.global_to_chunk5 56 (by decide)).trans hl
theorem bound867 : lowerHistoryBound 867 = bv867 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[66]? = some bv867 := Eq.refl (some bv867)
  exact (BoundCompact16.global_to_chunk5 66 (by decide)).trans hl
theorem bound871 : lowerHistoryBound 871 = bv871 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[70]? = some bv871 := Eq.refl (some bv871)
  exact (BoundCompact16.global_to_chunk5 70 (by decide)).trans hl
theorem bound959 : lowerHistoryBound 959 = bv959 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[158]? = some bv959 := Eq.refl (some bv959)
  exact (BoundCompact16.global_to_chunk5 158 (by decide)).trans hl
theorem bound1030 : lowerHistoryBound 1030 = bv1030 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[29]? = some bv1030 := Eq.refl (some bv1030)
  exact (BoundCompact16.global_to_chunk6 29).trans hl
theorem bound1032 : lowerHistoryBound 1032 = bv1032 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[31]? = some bv1032 := Eq.refl (some bv1032)
  exact (BoundCompact16.global_to_chunk6 31).trans hl
theorem bound1033 : lowerHistoryBound 1033 = bv1033 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[32]? = some bv1033 := Eq.refl (some bv1033)
  exact (BoundCompact16.global_to_chunk6 32).trans hl
theorem bound1076 : lowerHistoryBound 1076 = bv1076 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[75]? = some bv1076 := Eq.refl (some bv1076)
  exact (BoundCompact16.global_to_chunk6 75).trans hl
theorem bound1110 : lowerHistoryBound 1110 = bv1110 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[109]? = some bv1110 := Eq.refl (some bv1110)
  exact (BoundCompact16.global_to_chunk6 109).trans hl
theorem bound1115 : lowerHistoryBound 1115 = bv1115 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[114]? = some bv1115 := Eq.refl (some bv1115)
  exact (BoundCompact16.global_to_chunk6 114).trans hl
theorem bound1140 : lowerHistoryBound 1140 = bv1140 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[139]? = some bv1140 := Eq.refl (some bv1140)
  exact (BoundCompact16.global_to_chunk6 139).trans hl
theorem bound1162 : lowerHistoryBound 1162 = bv1162 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[161]? = some bv1162 := Eq.refl (some bv1162)
  exact (BoundCompact16.global_to_chunk6 161).trans hl
end M7ContinueSep17.Initial20260918.B1085_1090

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
theorem catalogListH : catalogRecords .initial = [

  ⟨.initial,1,0,(-1),false,1018,410⟩,
  ⟨.initial,1,1,(-1),false,1016,410⟩,
  ⟨.initial,1,2,(-1),false,1019,410⟩,
  ⟨.initial,2,0,(-1),false,1021,504⟩,
  ⟨.initial,2,1,(-1),false,1017,504⟩,
  ⟨.initial,2,2,(-1),false,1022,504⟩,
  ⟨.initial,3,0,(-1),false,830,405⟩,
  ⟨.initial,3,1,(-1),false,829,405⟩,
  ⟨.initial,3,2,(-1),false,831,405⟩,
  ⟨.initial,4,0,(-1),false,822,476⟩,
  ⟨.initial,4,1,(-1),false,821,476⟩,
  ⟨.initial,4,2,(-1),false,823,476⟩,
  ⟨.initial,5,0,(-1),false,826,489⟩,
  ⟨.initial,5,1,(-1),false,825,489⟩,
  ⟨.initial,5,2,(-1),false,827,489⟩,
  ⟨.initial,6,0,(-1),false,834,504⟩,
  ⟨.initial,6,1,(-1),false,833,504⟩,
  ⟨.initial,6,2,(-1),false,835,504⟩,
  ⟨.initial,7,0,(-1),false,818,421⟩,
  ⟨.initial,7,1,(-1),false,817,421⟩,
  ⟨.initial,7,2,(-1),false,819,421⟩,
  ⟨.initial,8,0,(-1),false,802,369⟩,
  ⟨.initial,8,1,(-1),false,798,369⟩,
  ⟨.initial,8,2,(-1),false,801,369⟩,
  ⟨.initial,8,3,(-1),false,797,369⟩,
  ⟨.initial,8,4,(-1),false,803,369⟩,
  ⟨.initial,8,5,(-1),false,799,369⟩,
  ⟨.initial,9,0,(-1),false,794,454⟩,
  ⟨.initial,9,1,(-1),false,786,454⟩,
  ⟨.initial,9,2,(-1),false,790,454⟩,
  ⟨.initial,9,3,(-1),false,782,454⟩,
  ⟨.initial,9,4,(-1),false,793,454⟩,
  ⟨.initial,9,5,(-1),false,785,454⟩,
  ⟨.initial,9,6,(-1),false,789,454⟩,
  ⟨.initial,9,7,(-1),false,781,454⟩,
  ⟨.initial,9,8,(-1),false,795,454⟩,
  ⟨.initial,9,9,(-1),false,787,454⟩,
  ⟨.initial,9,10,(-1),false,791,454⟩,
  ⟨.initial,9,11,(-1),false,783,454⟩,
  ⟨.initial,10,0,(-1),false,814,386⟩,
  ⟨.initial,10,1,(-1),false,813,386⟩,
  ⟨.initial,10,2,(-1),false,815,386⟩,
  ⟨.initial,11,0,(-1),false,810,467⟩,
  ⟨.initial,11,1,(-1),false,806,467⟩,
  ⟨.initial,11,2,(-1),false,809,467⟩,
  ⟨.initial,11,3,(-1),false,805,467⟩,
  ⟨.initial,11,4,(-1),false,811,467⟩,
  ⟨.initial,11,5,(-1),false,807,467⟩,
  ⟨.initial,12,0,(-1),false,730,416⟩,
  ⟨.initial,13,0,(-1),false,670,514⟩,
  ⟨.initial,13,1,(-1),false,668,514⟩,
  ⟨.initial,14,0,(-1),false,768,412⟩,
  ⟨.initial,15,0,(-1),false,764,488⟩,
  ⟨.initial,16,0,(-1),false,766,501⟩,
  ⟨.initial,17,0,(-1),false,672,514⟩,
  ⟨.initial,18,0,(-1),false,762,326⟩,
  ⟨.initial,19,0,(-1),false,663,366⟩,
  ⟨.initial,20,0,(-1),false,661,453⟩,
  ⟨.initial,21,0,(-1),false,760,375⟩,
  ⟨.initial,21,1,(-1),false,758,375⟩,
  ⟨.initial,22,0,(-1),false,750,460⟩,
  ⟨.initial,22,1,(-1),false,746,460⟩,
  ⟨.initial,22,2,(-1),false,748,460⟩,
  ⟨.initial,22,3,(-1),false,744,460⟩,
  ⟨.initial,23,0,(-1),false,756,392⟩,
  ⟨.initial,24,0,(-1),false,754,478⟩,
  ⟨.initial,24,1,(-1),false,752,478⟩,
  ⟨.initial,25,0,(-1),false,558,423⟩,
  ⟨.initial,26,0,(-1),false,557,410⟩,
  ⟨.initial,27,0,(-1),false,559,504⟩,
  ⟨.initial,28,0,(-1),false,543,416⟩,
  ⟨.initial,28,1,(-1),false,542,416⟩,
  ⟨.initial,29,0,(-1),false,533,514⟩,
  ⟨.initial,29,1,(-1),false,531,514⟩,
  ⟨.initial,29,2,(-1),false,532,514⟩,
  ⟨.initial,29,3,(-1),false,530,514⟩,
  ⟨.initial,30,0,(-1),false,554,423⟩,
  ⟨.initial,31,0,(-1),false,549,518⟩,
  ⟨.initial,31,1,(-1),false,548,518⟩,
  ⟨.initial,32,0,(-1),false,527,418⟩,
  ⟨.initial,33,0,(-1),false,518,503⟩,
  ⟨.initial,34,0,(-1),false,524,510⟩,
  ⟨.initial,35,0,(-1),false,521,518⟩,
  ⟨.initial,36,0,(-1),false,832,405⟩,
  ⟨.initial,37,0,(-1),false,824,476⟩,
  ⟨.initial,38,0,(-1),false,828,489⟩,
  ⟨.initial,39,0,(-1),false,836,504⟩,
  ⟨.initial,40,0,(-1),false,820,421⟩,
  ⟨.initial,41,0,(-1),false,804,369⟩,
  ⟨.initial,41,1,(-1),false,800,369⟩,
  ⟨.initial,42,0,(-1),false,796,454⟩,
  ⟨.initial,42,1,(-1),false,788,454⟩,
  ⟨.initial,42,2,(-1),false,792,454⟩,
  ⟨.initial,42,3,(-1),false,784,454⟩,
  ⟨.initial,43,0,(-1),false,816,386⟩,
  ⟨.initial,44,0,(-1),false,812,467⟩,
  ⟨.initial,44,1,(-1),false,808,467⟩,
  ⟨.initial,45,0,(-1),false,1020,410⟩,
  ⟨.initial,46,0,(-1),false,1023,504⟩,
  ⟨.initial,47,0,(-1),false,769,412⟩,
  ⟨.initial,48,0,(-1),false,765,488⟩,
  ⟨.initial,49,0,(-1),false,767,501⟩,
  ⟨.initial,50,0,(-1),false,673,514⟩,
  ⟨.initial,51,0,(-1),false,763,326⟩,
  ⟨.initial,52,0,(-1),false,664,366⟩,
  ⟨.initial,53,0,(-1),false,662,453⟩,
  ⟨.initial,54,0,(-1),false,761,375⟩,
  ⟨.initial,54,1,(-1),false,759,375⟩,
  ⟨.initial,55,0,(-1),false,751,460⟩,
  ⟨.initial,55,1,(-1),false,747,460⟩,
  ⟨.initial,55,2,(-1),false,749,460⟩,
  ⟨.initial,55,3,(-1),false,745,460⟩,
  ⟨.initial,56,0,(-1),false,757,392⟩,
  ⟨.initial,57,0,(-1),false,755,478⟩,
  ⟨.initial,57,1,(-1),false,753,478⟩,
  ⟨.initial,58,0,(-1),false,731,524⟩,
  ⟨.initial,59,0,(-1),false,671,514⟩,
  ⟨.initial,59,1,(-1),false,669,514⟩,
  ⟨.initial,60,0,(-1),false,593,418⟩,
  ⟨.initial,61,0,(-1),false,590,503⟩,
  ⟨.initial,62,0,(-1),false,592,510⟩,
  ⟨.initial,63,0,(-1),false,591,518⟩,
  ⟨.initial,64,0,(-1),false,589,332⟩,
  ⟨.initial,65,0,(-1),false,579,379⟩,
  ⟨.initial,66,0,(-1),false,578,466⟩,
  ⟨.initial,67,0,(-1),false,588,388⟩,
  ⟨.initial,67,1,(-1),false,587,388⟩,
  ⟨.initial,68,0,(-1),false,586,475⟩,
  ⟨.initial,68,1,(-1),false,584,475⟩,
  ⟨.initial,68,2,(-1),false,585,475⟩,
  ⟨.initial,68,3,(-1),false,583,475⟩,
  ⟨.initial,69,0,(-1),false,582,402⟩,
  ⟨.initial,70,0,(-1),false,581,491⟩,
  ⟨.initial,70,1,(-1),false,580,491⟩,
  ⟨.initial,71,0,(-1),false,660,423⟩,
  ⟨.initial,72,0,(-1),false,659,518⟩,
  ⟨.initial,72,1,(-1),false,658,518⟩,
  ⟨.initial,73,0,(-1),false,779,503⟩,
  ⟨.initial,74,0,(-1),false,936,330⟩,
  ⟨.initial,75,0,(-1),false,922,356⟩,
  ⟨.initial,76,0,(-1),false,920,437⟩,
  ⟨.initial,77,0,(-1),false,934,364⟩,
  ⟨.initial,77,1,(-1),false,932,364⟩,
  ⟨.initial,78,0,(-1),false,930,443⟩,
  ⟨.initial,78,1,(-1),false,926,443⟩,
  ⟨.initial,78,2,(-1),false,928,443⟩,
  ⟨.initial,78,3,(-1),false,924,443⟩,
  ⟨.initial,79,0,(-1),false,774,381⟩,
  ⟨.initial,80,0,(-1),false,772,462⟩,
  ⟨.initial,80,1,(-1),false,770,462⟩,
  ⟨.initial,81,0,(-1),false,918,371⟩,
  ⟨.initial,82,0,(-1),false,916,447⟩,
  ⟨.initial,83,0,(-1),false,914,462⟩,
  ⟨.initial,84,0,(-1),false,939,510⟩,
  ⟨.initial,85,0,(-1),false,896,336⟩,
  ⟨.initial,86,0,(-1),false,875,362⟩,
  ⟨.initial,87,0,(-1),false,872,445⟩,
  ⟨.initial,88,0,(-1),false,893,373⟩,
  ⟨.initial,88,1,(-1),false,890,373⟩,
  ⟨.initial,89,0,(-1),false,887,456⟩,
  ⟨.initial,89,1,(-1),false,881,456⟩,
  ⟨.initial,89,2,(-1),false,884,456⟩,
  ⟨.initial,89,3,(-1),false,878,456⟩,
  ⟨.initial,90,0,(-1),false,860,390⟩,
  ⟨.initial,91,0,(-1),false,857,471⟩,
  ⟨.initial,91,1,(-1),false,854,471⟩,
  ⟨.initial,92,0,(-1),false,869,383⟩,
  ⟨.initial,93,0,(-1),false,851,449⟩,
  ⟨.initial,94,0,(-1),false,866,458⟩,
  ⟨.initial,95,0,(-1),false,863,471⟩,
  ⟨.initial,96,0,(-1),false,1015,371⟩,
  ⟨.initial,97,0,(-1),false,1014,447⟩,
  ⟨.initial,98,0,(-1),false,1013,462⟩,
  ⟨.initial,99,0,(-1),false,1012,342⟩,
  ⟨.initial,100,0,(-1),false,1002,344⟩,
  ⟨.initial,101,0,(-1),false,1001,425⟩,
  ⟨.initial,102,0,(-1),false,1011,348⟩,
  ⟨.initial,102,1,(-1),false,1010,348⟩,
  ⟨.initial,103,0,(-1),false,1009,427⟩,
  ⟨.initial,103,1,(-1),false,1007,427⟩,
  ⟨.initial,103,2,(-1),false,1008,427⟩,
  ⟨.initial,103,3,(-1),false,1006,427⟩,
  ⟨.initial,104,0,(-1),false,1005,354⟩,
  ⟨.initial,105,0,(-1),false,1004,433⟩,
  ⟨.initial,105,1,(-1),false,1003,433⟩,
  ⟨.initial,106,0,(-1),false,778,499⟩,
  ⟨.initial,107,0,(-1),false,777,462⟩,
  ⟨.initial,107,1,(-1),false,776,462⟩,
  ⟨.initial,108,0,(-1),false,937,330⟩,
  ⟨.initial,109,0,(-1),false,923,356⟩,
  ⟨.initial,110,0,(-1),false,921,437⟩,
  ⟨.initial,111,0,(-1),false,935,364⟩,
  ⟨.initial,111,1,(-1),false,933,364⟩,
  ⟨.initial,112,0,(-1),false,931,443⟩,
  ⟨.initial,112,1,(-1),false,927,443⟩,
  ⟨.initial,112,2,(-1),false,929,443⟩,
  ⟨.initial,112,3,(-1),false,925,443⟩,
  ⟨.initial,113,0,(-1),false,775,381⟩,
  ⟨.initial,114,0,(-1),false,773,462⟩,
  ⟨.initial,114,1,(-1),false,771,462⟩,
  ⟨.initial,115,0,(-1),false,919,371⟩,
  ⟨.initial,116,0,(-1),false,917,447⟩,
  ⟨.initial,117,0,(-1),false,915,462⟩,
  ⟨.initial,118,0,(-1),false,780,503⟩,
  ⟨.initial,119,0,(-1),false,1000,383⟩,
  ⟨.initial,119,1,(-1),false,998,383⟩,
  ⟨.initial,119,2,(-1),false,999,383⟩,
  ⟨.initial,119,3,(-1),false,997,383⟩,
  ⟨.initial,120,0,(-1),false,901,449⟩,
  ⟨.initial,120,1,(-1),false,899,449⟩,
  ⟨.initial,120,2,(-1),false,900,449⟩,
  ⟨.initial,120,3,(-1),false,898,449⟩,
  ⟨.initial,121,0,(-1),false,996,458⟩,
  ⟨.initial,121,1,(-1),false,994,458⟩,
  ⟨.initial,121,2,(-1),false,995,458⟩,
  ⟨.initial,121,3,(-1),false,993,458⟩,
  ⟨.initial,122,0,(-1),false,992,471⟩,
  ⟨.initial,122,1,(-1),false,990,471⟩,
  ⟨.initial,122,2,(-1),false,991,471⟩,
  ⟨.initial,122,3,(-1),false,989,471⟩,
  ⟨.initial,123,0,(-1),false,988,340⟩,
  ⟨.initial,123,1,(-1),false,986,340⟩,
  ⟨.initial,123,2,(-1),false,987,340⟩,
  ⟨.initial,123,3,(-1),false,985,340⟩,
  ⟨.initial,124,0,(-1),false,948,346⟩,
  ⟨.initial,124,1,(-1),false,946,346⟩,
  ⟨.initial,124,2,(-1),false,947,346⟩,
  ⟨.initial,124,3,(-1),false,945,346⟩,
  ⟨.initial,125,0,(-1),false,944,429⟩,
  ⟨.initial,125,1,(-1),false,942,429⟩,
  ⟨.initial,125,2,(-1),false,943,429⟩,
  ⟨.initial,125,3,(-1),false,941,429⟩,
  ⟨.initial,126,0,(-1),false,984,350⟩,
  ⟨.initial,126,1,(-1),false,980,350⟩,
  ⟨.initial,126,2,(-1),false,982,350⟩,
  ⟨.initial,126,3,(-1),false,978,350⟩,
  ⟨.initial,126,4,(-1),false,983,350⟩,
  ⟨.initial,126,5,(-1),false,979,350⟩,
  ⟨.initial,126,6,(-1),false,981,350⟩,
  ⟨.initial,126,7,(-1),false,977,350⟩,
  ⟨.initial,127,0,(-1),false,976,431⟩,
  ⟨.initial,127,1,(-1),false,968,431⟩,
  ⟨.initial,127,2,(-1),false,972,431⟩,
  ⟨.initial,127,3,(-1),false,964,431⟩,
  ⟨.initial,127,4,(-1),false,974,431⟩,
  ⟨.initial,127,5,(-1),false,966,431⟩,
  ⟨.initial,127,6,(-1),false,970,431⟩,
  ⟨.initial,127,7,(-1),false,962,431⟩,
  ⟨.initial,127,8,(-1),false,975,431⟩,
  ⟨.initial,127,9,(-1),false,967,431⟩,
  ⟨.initial,127,10,(-1),false,971,431⟩,
  ⟨.initial,127,11,(-1),false,963,431⟩,
  ⟨.initial,127,12,(-1),false,973,431⟩,
  ⟨.initial,127,13,(-1),false,965,431⟩,
  ⟨.initial,127,14,(-1),false,969,431⟩,
  ⟨.initial,127,15,(-1),false,961,431⟩,
  ⟨.initial,128,0,(-1),false,960,360⟩,
  ⟨.initial,128,1,(-1),false,958,360⟩,
  ⟨.initial,128,2,(-1),false,959,360⟩,
  ⟨.initial,128,3,(-1),false,957,360⟩,
  ⟨.initial,129,0,(-1),false,956,439⟩,
  ⟨.initial,129,1,(-1),false,952,439⟩,
  ⟨.initial,129,2,(-1),false,954,439⟩,
  ⟨.initial,129,3,(-1),false,950,439⟩,
  ⟨.initial,129,4,(-1),false,955,439⟩,
  ⟨.initial,129,5,(-1),false,951,439⟩,
  ⟨.initial,129,6,(-1),false,953,439⟩,
  ⟨.initial,129,7,(-1),false,949,439⟩,
  ⟨.initial,130,0,(-1),false,913,506⟩,
  ⟨.initial,130,1,(-1),false,911,377⟩,
  ⟨.initial,130,2,(-1),false,912,506⟩,
  ⟨.initial,130,3,(-1),false,910,377⟩,
  ⟨.initial,131,0,(-1),false,909,471⟩,
  ⟨.initial,131,1,(-1),false,905,471⟩,
  ⟨.initial,131,2,(-1),false,907,471⟩,
  ⟨.initial,131,3,(-1),false,903,471⟩,
  ⟨.initial,131,4,(-1),false,908,471⟩,
  ⟨.initial,131,5,(-1),false,904,471⟩,
  ⟨.initial,131,6,(-1),false,906,471⟩,
  ⟨.initial,131,7,(-1),false,902,471⟩,
  ⟨.initial,132,0,(-1),false,897,512⟩,
  ⟨.initial,132,1,(-1),false,895,336⟩,
  ⟨.initial,133,0,(-1),false,876,362⟩,
  ⟨.initial,133,1,(-1),false,874,362⟩,
  ⟨.initial,134,0,(-1),false,873,445⟩,
  ⟨.initial,134,1,(-1),false,871,445⟩,
  ⟨.initial,135,0,(-1),false,894,373⟩,
  ⟨.initial,135,1,(-1),false,891,373⟩,
  ⟨.initial,135,2,(-1),false,892,373⟩,
  ⟨.initial,135,3,(-1),false,889,373⟩,
  ⟨.initial,136,0,(-1),false,888,456⟩,
  ⟨.initial,136,1,(-1),false,882,456⟩,
  ⟨.initial,136,2,(-1),false,885,456⟩,
  ⟨.initial,136,3,(-1),false,879,456⟩,
  ⟨.initial,136,4,(-1),false,886,456⟩,
  ⟨.initial,136,5,(-1),false,880,456⟩,
  ⟨.initial,136,6,(-1),false,883,456⟩,
  ⟨.initial,136,7,(-1),false,877,456⟩,
  ⟨.initial,137,0,(-1),false,861,390⟩,
  ⟨.initial,137,1,(-1),false,859,390⟩,
  ⟨.initial,138,0,(-1),false,858,471⟩,
  ⟨.initial,138,1,(-1),false,855,471⟩,
  ⟨.initial,138,2,(-1),false,856,471⟩,
  ⟨.initial,138,3,(-1),false,853,471⟩,
  ⟨.initial,139,0,(-1),false,870,383⟩,
  ⟨.initial,139,1,(-1),false,868,383⟩,
  ⟨.initial,140,0,(-1),false,852,449⟩,
  ⟨.initial,140,1,(-1),false,850,449⟩,
  ⟨.initial,141,0,(-1),false,867,458⟩,
  ⟨.initial,141,1,(-1),false,865,458⟩,
  ⟨.initial,142,0,(-1),false,864,471⟩,
  ⟨.initial,142,1,(-1),false,862,471⟩,
  ⟨.initial,143,0,(-1),false,940,512⟩,
  ⟨.initial,143,1,(-1),false,938,510⟩,
  ⟨.initial,144,0,(-1),false,722,396⟩,
  ⟨.initial,144,1,(-1),false,721,396⟩,
  ⟨.initial,145,0,(-1),false,692,464⟩,
  ⟨.initial,145,1,(-1),false,691,464⟩,
  ⟨.initial,146,0,(-1),false,720,473⟩,
  ⟨.initial,146,1,(-1),false,719,473⟩,
  ⟨.initial,147,0,(-1),false,718,491⟩,
  ⟨.initial,147,1,(-1),false,717,491⟩,
  ⟨.initial,148,0,(-1),false,716,338⟩,
  ⟨.initial,148,1,(-1),false,715,338⟩,
  ⟨.initial,149,0,(-1),false,696,352⟩,
  ⟨.initial,149,1,(-1),false,695,352⟩,
  ⟨.initial,150,0,(-1),false,694,435⟩,
  ⟨.initial,150,1,(-1),false,693,435⟩,
  ⟨.initial,151,0,(-1),false,714,358⟩,
  ⟨.initial,151,1,(-1),false,712,358⟩,
  ⟨.initial,151,2,(-1),false,713,358⟩,
  ⟨.initial,151,3,(-1),false,711,358⟩,
  ⟨.initial,152,0,(-1),false,710,441⟩,
  ⟨.initial,152,1,(-1),false,706,441⟩,
  ⟨.initial,152,2,(-1),false,708,441⟩,
  ⟨.initial,152,3,(-1),false,704,441⟩,
  ⟨.initial,152,4,(-1),false,709,441⟩,
  ⟨.initial,152,5,(-1),false,705,441⟩,
  ⟨.initial,152,6,(-1),false,707,441⟩,
  ⟨.initial,152,7,(-1),false,703,441⟩,
  ⟨.initial,153,0,(-1),false,702,368⟩,
  ⟨.initial,153,1,(-1),false,701,368⟩,
  ⟨.initial,154,0,(-1),false,700,451⟩,
  ⟨.initial,154,1,(-1),false,698,451⟩,
  ⟨.initial,154,2,(-1),false,699,451⟩,
  ⟨.initial,154,3,(-1),false,697,451⟩,
  ⟨.initial,155,0,(-1),false,728,516⟩,
  ⟨.initial,155,1,(-1),false,727,402⟩,
  ⟨.initial,156,0,(-1),false,726,491⟩,
  ⟨.initial,156,1,(-1),false,724,491⟩,
  ⟨.initial,156,2,(-1),false,725,491⟩,
  ⟨.initial,156,3,(-1),false,723,491⟩,
  ⟨.initial,157,0,(-1),false,689,332⟩,
  ⟨.initial,158,0,(-1),false,675,379⟩,
  ⟨.initial,159,0,(-1),false,674,466⟩,
  ⟨.initial,160,0,(-1),false,688,388⟩,
  ⟨.initial,160,1,(-1),false,687,388⟩,
  ⟨.initial,161,0,(-1),false,686,475⟩,
  ⟨.initial,161,1,(-1),false,684,475⟩,
  ⟨.initial,161,2,(-1),false,685,475⟩,
  ⟨.initial,161,3,(-1),false,683,475⟩,
  ⟨.initial,162,0,(-1),false,682,402⟩,
  ⟨.initial,163,0,(-1),false,681,491⟩,
  ⟨.initial,163,1,(-1),false,680,491⟩,
  ⟨.initial,164,0,(-1),false,679,396⟩,
  ⟨.initial,165,0,(-1),false,676,464⟩,
  ⟨.initial,166,0,(-1),false,678,473⟩,
  ⟨.initial,167,0,(-1),false,677,491⟩,
  ⟨.initial,168,0,(-1),false,690,324⟩,
  ⟨.initial,169,0,(-1),false,656,418⟩,
  ⟨.initial,169,1,(-1),false,654,418⟩,
  ⟨.initial,170,0,(-1),false,644,503⟩,
  ⟨.initial,170,1,(-1),false,642,503⟩,
  ⟨.initial,171,0,(-1),false,652,510⟩,
  ⟨.initial,171,1,(-1),false,650,510⟩,
  ⟨.initial,172,0,(-1),false,648,518⟩,
  ⟨.initial,172,1,(-1),false,646,518⟩,
  ⟨.initial,173,0,(-1),false,640,332⟩,
  ⟨.initial,173,1,(-1),false,638,332⟩,
  ⟨.initial,174,0,(-1),false,600,379⟩,
  ⟨.initial,174,1,(-1),false,598,379⟩,
  ⟨.initial,175,0,(-1),false,596,466⟩,
  ⟨.initial,175,1,(-1),false,594,466⟩,
  ⟨.initial,176,0,(-1),false,636,388⟩,
  ⟨.initial,176,1,(-1),false,632,388⟩,
  ⟨.initial,176,2,(-1),false,634,388⟩,
  ⟨.initial,176,3,(-1),false,630,388⟩,
  ⟨.initial,177,0,(-1),false,628,475⟩,
  ⟨.initial,177,1,(-1),false,620,475⟩,
  ⟨.initial,177,2,(-1),false,624,475⟩,
  ⟨.initial,177,3,(-1),false,616,475⟩,
  ⟨.initial,177,4,(-1),false,626,475⟩,
  ⟨.initial,177,5,(-1),false,618,475⟩,
  ⟨.initial,177,6,(-1),false,622,475⟩,
  ⟨.initial,177,7,(-1),false,614,475⟩,
  ⟨.initial,178,0,(-1),false,612,402⟩,
  ⟨.initial,178,1,(-1),false,610,402⟩,
  ⟨.initial,179,0,(-1),false,608,491⟩,
  ⟨.initial,179,1,(-1),false,604,491⟩,
  ⟨.initial,179,2,(-1),false,606,491⟩,
  ⟨.initial,179,3,(-1),false,602,491⟩,
  ⟨.initial,180,0,(-1),false,848,526⟩,
  ⟨.initial,180,1,(-1),false,846,420⟩,
  ⟨.initial,181,0,(-1),false,843,518⟩,
  ⟨.initial,181,1,(-1),false,839,518⟩,
  ⟨.initial,181,2,(-1),false,841,518⟩,
  ⟨.initial,181,3,(-1),false,837,518⟩,
  ⟨.initial,182,0,(-1),true,0,0⟩,
  ⟨.initial,183,0,(-1),false,560,410⟩,
  ⟨.initial,184,0,(-1),false,561,504⟩,
  ⟨.initial,185,0,(-1),false,546,416⟩,
  ⟨.initial,185,1,(-1),false,544,416⟩,
  ⟨.initial,186,0,(-1),false,540,514⟩,
  ⟨.initial,186,1,(-1),false,536,514⟩,
  ⟨.initial,186,2,(-1),false,538,514⟩,
  ⟨.initial,186,3,(-1),false,534,514⟩,
  ⟨.initial,187,0,(-1),false,555,420⟩,
  ⟨.initial,188,0,(-1),false,552,518⟩,
  ⟨.initial,188,1,(-1),false,550,518⟩,
  ⟨.initial,189,0,(-1),false,528,418⟩,
  ⟨.initial,190,0,(-1),false,519,503⟩,
  ⟨.initial,191,0,(-1),false,525,510⟩,
  ⟨.initial,192,0,(-1),false,522,518⟩,
  ⟨.initial,193,0,(-1),false,1024,161⟩,
  ⟨.initial,194,0,(-1),false,577,334⟩,
  ⟨.initial,195,0,(-1),false,567,398⟩,
  ⟨.initial,196,0,(-1),false,566,484⟩,
  ⟨.initial,197,0,(-1),false,576,404⟩,
  ⟨.initial,197,1,(-1),false,575,404⟩,
  ⟨.initial,198,0,(-1),false,574,493⟩,
  ⟨.initial,198,1,(-1),false,572,493⟩,
  ⟨.initial,198,2,(-1),false,573,493⟩,
  ⟨.initial,198,3,(-1),false,571,493⟩,
  ⟨.initial,199,0,(-1),false,570,414⟩,
  ⟨.initial,200,0,(-1),false,569,508⟩,
  ⟨.initial,200,1,(-1),false,568,508⟩,
  ⟨.initial,201,0,(-1),false,565,409⟩,
  ⟨.initial,202,0,(-1),false,562,486⟩,
  ⟨.initial,203,0,(-1),false,564,495⟩,
  ⟨.initial,204,0,(-1),false,563,508⟩,
  ⟨.initial,205,0,(-1),false,845,522⟩,
  ⟨.initial,206,0,(-1),false,743,328⟩,
  ⟨.initial,207,0,(-1),false,736,385⟩,
  ⟨.initial,208,0,(-1),false,735,469⟩,
  ⟨.initial,209,0,(-1),false,742,394⟩,
  ⟨.initial,209,1,(-1),false,741,394⟩,
  ⟨.initial,210,0,(-1),false,740,480⟩,
  ⟨.initial,210,1,(-1),false,738,480⟩,
  ⟨.initial,210,2,(-1),false,739,480⟩,
  ⟨.initial,210,3,(-1),false,737,480⟩,
  ⟨.initial,211,0,(-1),false,667,407⟩,
  ⟨.initial,212,0,(-1),false,666,497⟩,
  ⟨.initial,212,1,(-1),false,665,497⟩,
  ⟨.initial,213,0,(-1),false,734,400⟩,
  ⟨.initial,214,0,(-1),false,733,482⟩,
  ⟨.initial,215,0,(-1),false,732,497⟩,
  ⟨.initial,216,0,(-1),false,729,520⟩,
  ⟨.initial,217,0,(-1),false,730,415⟩,
  ⟨.initial,218,0,(-1),false,670,513⟩,
  ⟨.initial,218,1,(-1),false,668,513⟩,
  ⟨.initial,219,0,(-1),false,768,411⟩,
  ⟨.initial,220,0,(-1),false,764,487⟩,
  ⟨.initial,221,0,(-1),false,766,500⟩,
  ⟨.initial,222,0,(-1),false,672,513⟩,
  ⟨.initial,223,0,(-1),false,762,325⟩,
  ⟨.initial,224,0,(-1),false,663,365⟩,
  ⟨.initial,225,0,(-1),false,661,452⟩,
  ⟨.initial,226,0,(-1),false,760,374⟩,
  ⟨.initial,226,1,(-1),false,758,374⟩,
  ⟨.initial,227,0,(-1),false,750,459⟩,
  ⟨.initial,227,1,(-1),false,746,459⟩,
  ⟨.initial,227,2,(-1),false,748,459⟩,
  ⟨.initial,227,3,(-1),false,744,459⟩,
  ⟨.initial,228,0,(-1),false,756,391⟩,
  ⟨.initial,229,0,(-1),false,754,477⟩,
  ⟨.initial,229,1,(-1),false,752,477⟩,
  ⟨.initial,230,0,(-1),false,558,422⟩,
  ⟨.initial,231,0,(-1),false,543,415⟩,
  ⟨.initial,231,1,(-1),false,542,415⟩,
  ⟨.initial,232,0,(-1),false,533,513⟩,
  ⟨.initial,232,1,(-1),false,531,513⟩,
  ⟨.initial,232,2,(-1),false,532,513⟩,
  ⟨.initial,232,3,(-1),false,530,513⟩,
  ⟨.initial,233,0,(-1),false,554,422⟩,
  ⟨.initial,234,0,(-1),false,549,517⟩,
  ⟨.initial,234,1,(-1),false,548,517⟩,
  ⟨.initial,235,0,(-1),false,527,417⟩,
  ⟨.initial,236,0,(-1),false,518,502⟩,
  ⟨.initial,237,0,(-1),false,524,509⟩,
  ⟨.initial,238,0,(-1),false,521,517⟩,
  ⟨.initial,239,0,(-1),false,769,411⟩,
  ⟨.initial,240,0,(-1),false,765,487⟩,
  ⟨.initial,241,0,(-1),false,767,500⟩,
  ⟨.initial,242,0,(-1),false,673,513⟩,
  ⟨.initial,243,0,(-1),false,763,325⟩,
  ⟨.initial,244,0,(-1),false,664,365⟩,
  ⟨.initial,245,0,(-1),false,662,452⟩,
  ⟨.initial,246,0,(-1),false,761,374⟩,
  ⟨.initial,246,1,(-1),false,759,374⟩,
  ⟨.initial,247,0,(-1),false,751,459⟩,
  ⟨.initial,247,1,(-1),false,747,459⟩,
  ⟨.initial,247,2,(-1),false,749,459⟩,
  ⟨.initial,247,3,(-1),false,745,459⟩,
  ⟨.initial,248,0,(-1),false,757,391⟩,
  ⟨.initial,249,0,(-1),false,755,477⟩,
  ⟨.initial,249,1,(-1),false,753,477⟩,
  ⟨.initial,250,0,(-1),false,731,523⟩,
  ⟨.initial,251,0,(-1),false,671,513⟩,
  ⟨.initial,251,1,(-1),false,669,513⟩,
  ⟨.initial,252,0,(-1),false,593,417⟩,
  ⟨.initial,253,0,(-1),false,590,502⟩,
  ⟨.initial,254,0,(-1),false,592,509⟩,
  ⟨.initial,255,0,(-1),false,591,517⟩,
  ⟨.initial,256,0,(-1),false,589,331⟩,
  ⟨.initial,257,0,(-1),false,579,378⟩,
  ⟨.initial,258,0,(-1),false,578,465⟩,
  ⟨.initial,259,0,(-1),false,588,387⟩,
  ⟨.initial,259,1,(-1),false,587,387⟩,
  ⟨.initial,260,0,(-1),false,586,474⟩,
  ⟨.initial,260,1,(-1),false,584,474⟩,
  ⟨.initial,260,2,(-1),false,585,474⟩,
  ⟨.initial,260,3,(-1),false,583,474⟩,
  ⟨.initial,261,0,(-1),false,582,401⟩,
  ⟨.initial,262,0,(-1),false,581,490⟩,
  ⟨.initial,262,1,(-1),false,580,490⟩,
  ⟨.initial,263,0,(-1),false,660,422⟩,
  ⟨.initial,264,0,(-1),false,659,517⟩,
  ⟨.initial,264,1,(-1),false,658,517⟩,
  ⟨.initial,265,0,(-1),false,779,502⟩,
  ⟨.initial,266,0,(-1),false,936,329⟩,
  ⟨.initial,267,0,(-1),false,922,355⟩,
  ⟨.initial,268,0,(-1),false,920,436⟩,
  ⟨.initial,269,0,(-1),false,934,363⟩,
  ⟨.initial,269,1,(-1),false,932,363⟩,
  ⟨.initial,270,0,(-1),false,930,442⟩,
  ⟨.initial,270,1,(-1),false,926,442⟩,
  ⟨.initial,270,2,(-1),false,928,442⟩,
  ⟨.initial,270,3,(-1),false,924,442⟩,
  ⟨.initial,271,0,(-1),false,774,380⟩,
  ⟨.initial,272,0,(-1),false,772,461⟩,
  ⟨.initial,272,1,(-1),false,770,461⟩,
  ⟨.initial,273,0,(-1),false,918,370⟩,
  ⟨.initial,274,0,(-1),false,916,446⟩,
  ⟨.initial,275,0,(-1),false,914,461⟩,
  ⟨.initial,276,0,(-1),false,939,509⟩,
  ⟨.initial,277,0,(-1),false,896,335⟩,
  ⟨.initial,278,0,(-1),false,875,361⟩,
  ⟨.initial,279,0,(-1),false,872,444⟩,
  ⟨.initial,280,0,(-1),false,893,372⟩,
  ⟨.initial,280,1,(-1),false,890,372⟩,
  ⟨.initial,281,0,(-1),false,887,455⟩,
  ⟨.initial,281,1,(-1),false,881,455⟩,
  ⟨.initial,281,2,(-1),false,884,455⟩,
  ⟨.initial,281,3,(-1),false,878,455⟩,
  ⟨.initial,282,0,(-1),false,860,389⟩,
  ⟨.initial,283,0,(-1),false,857,470⟩,
  ⟨.initial,283,1,(-1),false,854,470⟩,
  ⟨.initial,284,0,(-1),false,869,382⟩,
  ⟨.initial,285,0,(-1),false,851,448⟩,
  ⟨.initial,286,0,(-1),false,866,457⟩,
  ⟨.initial,287,0,(-1),false,863,470⟩,
  ⟨.initial,288,0,(-1),false,1015,370⟩,
  ⟨.initial,289,0,(-1),false,1014,446⟩,
  ⟨.initial,290,0,(-1),false,1013,461⟩,
  ⟨.initial,291,0,(-1),false,1012,341⟩,
  ⟨.initial,292,0,(-1),false,1002,343⟩,
  ⟨.initial,293,0,(-1),false,1001,424⟩,
  ⟨.initial,294,0,(-1),false,1011,347⟩,
  ⟨.initial,294,1,(-1),false,1010,347⟩,
  ⟨.initial,295,0,(-1),false,1009,426⟩,
  ⟨.initial,295,1,(-1),false,1007,426⟩,
  ⟨.initial,295,2,(-1),false,1008,426⟩,
  ⟨.initial,295,3,(-1),false,1006,426⟩,
  ⟨.initial,296,0,(-1),false,1005,353⟩,
  ⟨.initial,297,0,(-1),false,1004,432⟩,
  ⟨.initial,297,1,(-1),false,1003,432⟩,
  ⟨.initial,298,0,(-1),false,778,498⟩,
  ⟨.initial,299,0,(-1),false,777,461⟩,
  ⟨.initial,299,1,(-1),false,776,461⟩,
  ⟨.initial,300,0,(-1),false,937,329⟩,
  ⟨.initial,301,0,(-1),false,923,355⟩,
  ⟨.initial,302,0,(-1),false,921,436⟩,
  ⟨.initial,303,0,(-1),false,935,363⟩,
  ⟨.initial,303,1,(-1),false,933,363⟩,
  ⟨.initial,304,0,(-1),false,931,442⟩,
  ⟨.initial,304,1,(-1),false,927,442⟩,
  ⟨.initial,304,2,(-1),false,929,442⟩,
  ⟨.initial,304,3,(-1),false,925,442⟩,
  ⟨.initial,305,0,(-1),false,775,380⟩,
  ⟨.initial,306,0,(-1),false,773,461⟩,
  ⟨.initial,306,1,(-1),false,771,461⟩,
  ⟨.initial,307,0,(-1),false,919,370⟩,
  ⟨.initial,308,0,(-1),false,917,446⟩,
  ⟨.initial,309,0,(-1),false,915,461⟩,
  ⟨.initial,310,0,(-1),false,780,502⟩,
  ⟨.initial,311,0,(-1),false,1000,382⟩,
  ⟨.initial,311,1,(-1),false,998,382⟩,
  ⟨.initial,311,2,(-1),false,999,382⟩,
  ⟨.initial,311,3,(-1),false,997,382⟩,
  ⟨.initial,312,0,(-1),false,901,448⟩,
  ⟨.initial,312,1,(-1),false,899,448⟩,
  ⟨.initial,312,2,(-1),false,900,448⟩,
  ⟨.initial,312,3,(-1),false,898,448⟩,
  ⟨.initial,313,0,(-1),false,996,457⟩,
  ⟨.initial,313,1,(-1),false,994,457⟩,
  ⟨.initial,313,2,(-1),false,995,457⟩,
  ⟨.initial,313,3,(-1),false,993,457⟩,
  ⟨.initial,314,0,(-1),false,992,470⟩,
  ⟨.initial,314,1,(-1),false,990,470⟩,
  ⟨.initial,314,2,(-1),false,991,470⟩,
  ⟨.initial,314,3,(-1),false,989,470⟩,
  ⟨.initial,315,0,(-1),false,988,339⟩,
  ⟨.initial,315,1,(-1),false,986,339⟩,
  ⟨.initial,315,2,(-1),false,987,339⟩,
  ⟨.initial,315,3,(-1),false,985,339⟩,
  ⟨.initial,316,0,(-1),false,948,345⟩,
  ⟨.initial,316,1,(-1),false,946,345⟩,
  ⟨.initial,316,2,(-1),false,947,345⟩,
  ⟨.initial,316,3,(-1),false,945,345⟩,
  ⟨.initial,317,0,(-1),false,944,428⟩,
  ⟨.initial,317,1,(-1),false,942,428⟩,
  ⟨.initial,317,2,(-1),false,943,428⟩,
  ⟨.initial,317,3,(-1),false,941,428⟩,
  ⟨.initial,318,0,(-1),false,984,349⟩,
  ⟨.initial,318,1,(-1),false,980,349⟩,
  ⟨.initial,318,2,(-1),false,982,349⟩,
  ⟨.initial,318,3,(-1),false,978,349⟩,
  ⟨.initial,318,4,(-1),false,983,349⟩,
  ⟨.initial,318,5,(-1),false,979,349⟩,
  ⟨.initial,318,6,(-1),false,981,349⟩,
  ⟨.initial,318,7,(-1),false,977,349⟩,
  ⟨.initial,319,0,(-1),false,976,430⟩,
  ⟨.initial,319,1,(-1),false,968,430⟩,
  ⟨.initial,319,2,(-1),false,972,430⟩,
  ⟨.initial,319,3,(-1),false,964,430⟩,
  ⟨.initial,319,4,(-1),false,974,430⟩,
  ⟨.initial,319,5,(-1),false,966,430⟩,
  ⟨.initial,319,6,(-1),false,970,430⟩,
  ⟨.initial,319,7,(-1),false,962,430⟩,
  ⟨.initial,319,8,(-1),false,975,430⟩,
  ⟨.initial,319,9,(-1),false,967,430⟩,
  ⟨.initial,319,10,(-1),false,971,430⟩,
  ⟨.initial,319,11,(-1),false,963,430⟩,
  ⟨.initial,319,12,(-1),false,973,430⟩,
  ⟨.initial,319,13,(-1),false,965,430⟩,
  ⟨.initial,319,14,(-1),false,969,430⟩,
  ⟨.initial,319,15,(-1),false,961,430⟩,
  ⟨.initial,320,0,(-1),false,960,359⟩,
  ⟨.initial,320,1,(-1),false,958,359⟩,
  ⟨.initial,320,2,(-1),false,959,359⟩,
  ⟨.initial,320,3,(-1),false,957,359⟩,
  ⟨.initial,321,0,(-1),false,956,438⟩,
  ⟨.initial,321,1,(-1),false,952,438⟩,
  ⟨.initial,321,2,(-1),false,954,438⟩,
  ⟨.initial,321,3,(-1),false,950,438⟩,
  ⟨.initial,321,4,(-1),false,955,438⟩,
  ⟨.initial,321,5,(-1),false,951,438⟩,
  ⟨.initial,321,6,(-1),false,953,438⟩,
  ⟨.initial,321,7,(-1),false,949,438⟩,
  ⟨.initial,322,0,(-1),false,913,505⟩,
  ⟨.initial,322,1,(-1),false,911,376⟩,
  ⟨.initial,322,2,(-1),false,912,505⟩,
  ⟨.initial,322,3,(-1),false,910,376⟩,
  ⟨.initial,323,0,(-1),false,909,470⟩,
  ⟨.initial,323,1,(-1),false,905,470⟩,
  ⟨.initial,323,2,(-1),false,907,470⟩,
  ⟨.initial,323,3,(-1),false,903,470⟩,
  ⟨.initial,323,4,(-1),false,908,470⟩,
  ⟨.initial,323,5,(-1),false,904,470⟩,
  ⟨.initial,323,6,(-1),false,906,470⟩,
  ⟨.initial,323,7,(-1),false,902,470⟩,
  ⟨.initial,324,0,(-1),false,897,511⟩,
  ⟨.initial,324,1,(-1),false,895,335⟩,
  ⟨.initial,325,0,(-1),false,876,361⟩,
  ⟨.initial,325,1,(-1),false,874,361⟩,
  ⟨.initial,326,0,(-1),false,873,444⟩,
  ⟨.initial,326,1,(-1),false,871,444⟩,
  ⟨.initial,327,0,(-1),false,894,372⟩,
  ⟨.initial,327,1,(-1),false,891,372⟩,
  ⟨.initial,327,2,(-1),false,892,372⟩,
  ⟨.initial,327,3,(-1),false,889,372⟩,
  ⟨.initial,328,0,(-1),false,888,455⟩,
  ⟨.initial,328,1,(-1),false,882,455⟩,
  ⟨.initial,328,2,(-1),false,885,455⟩,
  ⟨.initial,328,3,(-1),false,879,455⟩,
  ⟨.initial,328,4,(-1),false,886,455⟩,
  ⟨.initial,328,5,(-1),false,880,455⟩,
  ⟨.initial,328,6,(-1),false,883,455⟩,
  ⟨.initial,328,7,(-1),false,877,455⟩,
  ⟨.initial,329,0,(-1),false,861,389⟩,
  ⟨.initial,329,1,(-1),false,859,389⟩,
  ⟨.initial,330,0,(-1),false,858,470⟩,
  ⟨.initial,330,1,(-1),false,855,470⟩,
  ⟨.initial,330,2,(-1),false,856,470⟩,
  ⟨.initial,330,3,(-1),false,853,470⟩,
  ⟨.initial,331,0,(-1),false,870,382⟩,
  ⟨.initial,331,1,(-1),false,868,382⟩,
  ⟨.initial,332,0,(-1),false,852,448⟩,
  ⟨.initial,332,1,(-1),false,850,448⟩,
  ⟨.initial,333,0,(-1),false,867,457⟩,
  ⟨.initial,333,1,(-1),false,865,457⟩,
  ⟨.initial,334,0,(-1),false,864,470⟩,
  ⟨.initial,334,1,(-1),false,862,470⟩,
  ⟨.initial,335,0,(-1),false,940,511⟩,
  ⟨.initial,335,1,(-1),false,938,509⟩,
  ⟨.initial,336,0,(-1),false,722,395⟩,
  ⟨.initial,336,1,(-1),false,721,395⟩,
  ⟨.initial,337,0,(-1),false,692,463⟩,
  ⟨.initial,337,1,(-1),false,691,463⟩,
  ⟨.initial,338,0,(-1),false,720,472⟩,
  ⟨.initial,338,1,(-1),false,719,472⟩,
  ⟨.initial,339,0,(-1),false,718,490⟩,
  ⟨.initial,339,1,(-1),false,717,490⟩,
  ⟨.initial,340,0,(-1),false,716,337⟩,
  ⟨.initial,340,1,(-1),false,715,337⟩,
  ⟨.initial,341,0,(-1),false,696,351⟩,
  ⟨.initial,341,1,(-1),false,695,351⟩,
  ⟨.initial,342,0,(-1),false,694,434⟩,
  ⟨.initial,342,1,(-1),false,693,434⟩,
  ⟨.initial,343,0,(-1),false,714,357⟩,
  ⟨.initial,343,1,(-1),false,712,357⟩,
  ⟨.initial,343,2,(-1),false,713,357⟩,
  ⟨.initial,343,3,(-1),false,711,357⟩,
  ⟨.initial,344,0,(-1),false,710,440⟩,
  ⟨.initial,344,1,(-1),false,706,440⟩,
  ⟨.initial,344,2,(-1),false,708,440⟩,
  ⟨.initial,344,3,(-1),false,704,440⟩,
  ⟨.initial,344,4,(-1),false,709,440⟩,
  ⟨.initial,344,5,(-1),false,705,440⟩,
  ⟨.initial,344,6,(-1),false,707,440⟩,
  ⟨.initial,344,7,(-1),false,703,440⟩,
  ⟨.initial,345,0,(-1),false,702,367⟩,
  ⟨.initial,345,1,(-1),false,701,367⟩,
  ⟨.initial,346,0,(-1),false,700,450⟩,
  ⟨.initial,346,1,(-1),false,698,450⟩,
  ⟨.initial,346,2,(-1),false,699,450⟩,
  ⟨.initial,346,3,(-1),false,697,450⟩,
  ⟨.initial,347,0,(-1),false,728,515⟩,
  ⟨.initial,347,1,(-1),false,727,401⟩,
  ⟨.initial,348,0,(-1),false,726,490⟩,
  ⟨.initial,348,1,(-1),false,724,490⟩,
  ⟨.initial,348,2,(-1),false,725,490⟩,
  ⟨.initial,348,3,(-1),false,723,490⟩,
  ⟨.initial,349,0,(-1),false,689,331⟩,
  ⟨.initial,350,0,(-1),false,675,378⟩,
  ⟨.initial,351,0,(-1),false,674,465⟩,
  ⟨.initial,352,0,(-1),false,688,387⟩,
  ⟨.initial,352,1,(-1),false,687,387⟩,
  ⟨.initial,353,0,(-1),false,686,474⟩,
  ⟨.initial,353,1,(-1),false,684,474⟩,
  ⟨.initial,353,2,(-1),false,685,474⟩,
  ⟨.initial,353,3,(-1),false,683,474⟩,
  ⟨.initial,354,0,(-1),false,682,401⟩,
  ⟨.initial,355,0,(-1),false,681,490⟩,
  ⟨.initial,355,1,(-1),false,680,490⟩,
  ⟨.initial,356,0,(-1),false,679,395⟩,
  ⟨.initial,357,0,(-1),false,676,463⟩,
  ⟨.initial,358,0,(-1),false,678,472⟩,
  ⟨.initial,359,0,(-1),false,677,490⟩,
  ⟨.initial,360,0,(-1),false,690,323⟩,
  ⟨.initial,361,0,(-1),false,657,417⟩,
  ⟨.initial,361,1,(-1),false,655,417⟩,
  ⟨.initial,362,0,(-1),false,645,502⟩,
  ⟨.initial,362,1,(-1),false,643,502⟩,
  ⟨.initial,363,0,(-1),false,653,509⟩,
  ⟨.initial,363,1,(-1),false,651,509⟩,
  ⟨.initial,364,0,(-1),false,649,517⟩,
  ⟨.initial,364,1,(-1),false,647,517⟩,
  ⟨.initial,365,0,(-1),false,641,331⟩,
  ⟨.initial,365,1,(-1),false,639,331⟩,
  ⟨.initial,366,0,(-1),false,601,378⟩,
  ⟨.initial,366,1,(-1),false,599,378⟩,
  ⟨.initial,367,0,(-1),false,597,465⟩,
  ⟨.initial,367,1,(-1),false,595,465⟩,
  ⟨.initial,368,0,(-1),false,637,387⟩,
  ⟨.initial,368,1,(-1),false,633,387⟩,
  ⟨.initial,368,2,(-1),false,635,387⟩,
  ⟨.initial,368,3,(-1),false,631,387⟩,
  ⟨.initial,369,0,(-1),false,629,474⟩,
  ⟨.initial,369,1,(-1),false,621,474⟩,
  ⟨.initial,369,2,(-1),false,625,474⟩,
  ⟨.initial,369,3,(-1),false,617,474⟩,
  ⟨.initial,369,4,(-1),false,627,474⟩,
  ⟨.initial,369,5,(-1),false,619,474⟩,
  ⟨.initial,369,6,(-1),false,623,474⟩,
  ⟨.initial,369,7,(-1),false,615,474⟩,
  ⟨.initial,370,0,(-1),false,613,401⟩,
  ⟨.initial,370,1,(-1),false,611,401⟩,
  ⟨.initial,371,0,(-1),false,609,490⟩,
  ⟨.initial,371,1,(-1),false,605,490⟩,
  ⟨.initial,371,2,(-1),false,607,490⟩,
  ⟨.initial,371,3,(-1),false,603,490⟩,
  ⟨.initial,372,0,(-1),false,849,525⟩,
  ⟨.initial,372,1,(-1),false,847,419⟩,
  ⟨.initial,373,0,(-1),false,844,517⟩,
  ⟨.initial,373,1,(-1),false,840,517⟩,
  ⟨.initial,373,2,(-1),false,842,517⟩,
  ⟨.initial,373,3,(-1),false,838,517⟩,
  ⟨.initial,374,0,(-1),true,0,0⟩,
  ⟨.initial,375,0,(-1),false,547,415⟩,
  ⟨.initial,375,1,(-1),false,545,415⟩,
  ⟨.initial,376,0,(-1),false,541,513⟩,
  ⟨.initial,376,1,(-1),false,537,513⟩,
  ⟨.initial,376,2,(-1),false,539,513⟩,
  ⟨.initial,376,3,(-1),false,535,513⟩,
  ⟨.initial,377,0,(-1),false,556,419⟩,
  ⟨.initial,378,0,(-1),false,553,517⟩,
  ⟨.initial,378,1,(-1),false,551,517⟩,
  ⟨.initial,379,0,(-1),false,529,417⟩,
  ⟨.initial,380,0,(-1),false,520,502⟩,
  ⟨.initial,381,0,(-1),false,526,509⟩,
  ⟨.initial,382,0,(-1),false,523,517⟩,
  ⟨.initial,383,0,(-1),false,1025,160⟩,
  ⟨.initial,384,0,(-1),false,577,333⟩,
  ⟨.initial,385,0,(-1),false,567,397⟩,
  ⟨.initial,386,0,(-1),false,566,483⟩,
  ⟨.initial,387,0,(-1),false,576,403⟩,
  ⟨.initial,387,1,(-1),false,575,403⟩,
  ⟨.initial,388,0,(-1),false,574,492⟩,
  ⟨.initial,388,1,(-1),false,572,492⟩,
  ⟨.initial,388,2,(-1),false,573,492⟩,
  ⟨.initial,388,3,(-1),false,571,492⟩,
  ⟨.initial,389,0,(-1),false,570,413⟩,
  ⟨.initial,390,0,(-1),false,569,507⟩,
  ⟨.initial,390,1,(-1),false,568,507⟩,
  ⟨.initial,391,0,(-1),false,565,408⟩,
  ⟨.initial,392,0,(-1),false,562,485⟩,
  ⟨.initial,393,0,(-1),false,564,494⟩,
  ⟨.initial,394,0,(-1),false,563,507⟩,
  ⟨.initial,395,0,(-1),false,845,521⟩,
  ⟨.initial,396,0,(-1),false,743,327⟩,
  ⟨.initial,397,0,(-1),false,736,384⟩,
  ⟨.initial,398,0,(-1),false,735,468⟩,
  ⟨.initial,399,0,(-1),false,742,393⟩,
  ⟨.initial,399,1,(-1),false,741,393⟩,
  ⟨.initial,400,0,(-1),false,740,479⟩,
  ⟨.initial,400,1,(-1),false,738,479⟩,
  ⟨.initial,400,2,(-1),false,739,479⟩,
  ⟨.initial,400,3,(-1),false,737,479⟩,
  ⟨.initial,401,0,(-1),false,667,406⟩,
  ⟨.initial,402,0,(-1),false,666,496⟩,
  ⟨.initial,402,1,(-1),false,665,496⟩,
  ⟨.initial,403,0,(-1),false,734,399⟩,
  ⟨.initial,404,0,(-1),false,733,481⟩,
  ⟨.initial,405,0,(-1),false,732,496⟩,
  ⟨.initial,406,0,(-1),false,729,519⟩

] := by rfl
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
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def recs1086 : List LowerHistoryRecord := [⟨.rightMixed,90,0,(-1),false,16,286⟩]
theorem records1086 : lowerHistoryRecordsFor (⟨.rightMixed,90,[3,1,3,1],([2],[3]),true,[(([1],[]),true)],([3,1,3,1,2],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1086 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 90)) = recs1086
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
noncomputable def recs1087 : List LowerHistoryRecord := [⟨.initial,1,0,(-1),false,1018,410⟩,⟨.initial,1,1,(-1),false,1016,410⟩,⟨.initial,1,2,(-1),false,1019,410⟩]
theorem records1087 : lowerHistoryRecordsFor (⟨.initial,1,[2],([1],[]),false,[(([3],[1]),true)],([2,1,3],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩ : LowerHistoryPath) = recs1087 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 1)) = recs1087
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1088 : List LowerHistoryRecord := [⟨.initial,2,0,(-1),false,1021,504⟩,⟨.initial,2,1,(-1),false,1017,504⟩,⟨.initial,2,2,(-1),false,1022,504⟩]
theorem records1088 : lowerHistoryRecordsFor (⟨.initial,2,[2],([1],[]),false,[(([3],[1]),true),(([],[1]),false)],([2,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩ : LowerHistoryPath) = recs1088 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 2)) = recs1088
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1089 : List LowerHistoryRecord := [⟨.initial,3,0,(-1),false,830,405⟩,⟨.initial,3,1,(-1),false,829,405⟩,⟨.initial,3,2,(-1),false,831,405⟩]
theorem records1089 : lowerHistoryRecordsFor (⟨.initial,3,[2],([1],[]),false,[(([3],[1]),false)],([2,1,3],[3,1,3,1]),(false,true),false,4,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩ : LowerHistoryPath) = recs1089 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 3)) = recs1089
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1090 : List LowerHistoryRecord := [⟨.initial,4,0,(-1),false,822,476⟩,⟨.initial,4,1,(-1),false,821,476⟩,⟨.initial,4,2,(-1),false,823,476⟩]
theorem records1090 : lowerHistoryRecordsFor (⟨.initial,4,[2],([1],[]),false,[(([3],[1]),false),(([3],[]),true)],([2,1,3,3],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩ : LowerHistoryPath) = recs1090 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 4)) = recs1090
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
end M7ContinueSep17.Initial20260918.B1085_1090

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
namespace M7ContinueSep17.Initial20260918.B1085_1090
theorem premise16 : lowerHistoryPremises[15]? = some ([1,3,260,293,296,371,440,843,857,867,871] : List Nat) := by
  have hg : lowerHistoryPremises[15]? = lowerHistoryPremises01[15]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 15 (by decide)
  exact hg.trans (by rfl)
theorem premise821 : lowerHistoryPremises[820]? = some ([37,65,132,240,327,371,433,538,679,727,799,832,839,843,959,1032,1033,1076,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[820]? = lowerHistoryPremises05[20]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 20 (by decide)
  exact hg.trans (by rfl)
theorem premise822 : lowerHistoryPremises[821]? = some ([37,65,132,245,327,371,433,538,679,727,799,832,839,843,959,1032,1033,1076,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[821]? = lowerHistoryPremises05[21]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 21 (by decide)
  exact hg.trans (by rfl)
theorem premise823 : lowerHistoryPremises[822]? = some ([37,65,132,261,327,371,433,538,679,727,799,832,839,843,959,1032,1033,1076,1162] : List Nat) := by
  have hg : lowerHistoryPremises[822]? = lowerHistoryPremises05[22]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 22 (by decide)
  exact hg.trans (by rfl)
theorem premise829 : lowerHistoryPremises[828]? = some ([37,132,217,240,371,433,727,799,832,839,843,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[828]? = lowerHistoryPremises05[28]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 28 (by decide)
  exact hg.trans (by rfl)
theorem premise830 : lowerHistoryPremises[829]? = some ([37,132,217,245,371,433,727,799,832,839,843,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[829]? = lowerHistoryPremises05[29]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 29 (by decide)
  exact hg.trans (by rfl)
theorem premise831 : lowerHistoryPremises[830]? = some ([37,132,217,261,371,433,727,799,832,839,843,1162] : List Nat) := by
  have hg : lowerHistoryPremises[830]? = lowerHistoryPremises05[30]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 30 (by decide)
  exact hg.trans (by rfl)
theorem premise1016 : lowerHistoryPremises[1015]? = some ([132,240,241,281,371,433,714,757,799,839,843,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1015]? = lowerHistoryPremises06[15]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 15 (by decide)
  exact hg.trans (by rfl)
theorem premise1017 : lowerHistoryPremises[1016]? = some ([132,240,280,281,371,431,433,701,714,777,799,839,843,1030,1110,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1016]? = lowerHistoryPremises06[16]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 16 (by decide)
  exact hg.trans (by rfl)
theorem premise1018 : lowerHistoryPremises[1017]? = some ([132,241,245,281,371,433,714,757,799,839,843,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1017]? = lowerHistoryPremises06[17]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 17 (by decide)
  exact hg.trans (by rfl)
theorem premise1019 : lowerHistoryPremises[1018]? = some ([132,241,261,281,371,433,714,757,799,839,843,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1018]? = lowerHistoryPremises06[18]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 18 (by decide)
  exact hg.trans (by rfl)
theorem premise1021 : lowerHistoryPremises[1020]? = some ([132,245,280,281,371,431,433,701,714,777,799,839,843,1030,1110,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1020]? = lowerHistoryPremises06[20]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 20 (by decide)
  exact hg.trans (by rfl)
theorem premise1022 : lowerHistoryPremises[1021]? = some ([132,261,280,281,371,431,433,701,714,777,799,839,843,1030,1110,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1021]? = lowerHistoryPremises06[21]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 21 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1085_1090
theorem witness286_projection : (lowerHistoryWitness 286).lowerBound = lowerHistoryBound 296 ∧ (lowerHistoryWitness 286).upperBound = lowerHistoryBound 843 ∧ (lowerHistoryWitness 286).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[85]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 296, lowerHistoryBound 843, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 296, lowerHistoryBound 843, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[285]? = lowerHistoryWitnesses02[85]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 85 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness405_projection : (lowerHistoryWitness 405).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 405).upperBound = lowerHistoryBound 727 ∧ (lowerHistoryWitness 405).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[4]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 727, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 727, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[404]? = lowerHistoryWitnesses03[4]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 4 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness410_projection : (lowerHistoryWitness 410).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 410).upperBound = lowerHistoryBound 757 ∧ (lowerHistoryWitness 410).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[9]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 757, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 757, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[409]? = lowerHistoryWitnesses03[9]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 9 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness476_projection : (lowerHistoryWitness 476).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 476).upperBound = lowerHistoryBound 959 ∧ (lowerHistoryWitness 476).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[75]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 959, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 959, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[475]? = lowerHistoryWitnesses03[75]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 75 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness504_projection : (lowerHistoryWitness 504).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 504).upperBound = lowerHistoryBound 1030 ∧ (lowerHistoryWitness 504).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[103]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 1030, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 1030, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[503]? = lowerHistoryWitnesses03[103]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 103 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 286 => (296,843)
  | 405 => (433,727)
  | 410 => (433,757)
  | 476 => (433,959)
  | 504 => (433,1030)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 16 => [1,3,260,293,296,371,440,843,857,867,871]
  | 821 => [37,65,132,240,327,371,433,538,679,727,799,832,839,843,959,1032,1033,1076,1115,1140,1162]
  | 822 => [37,65,132,245,327,371,433,538,679,727,799,832,839,843,959,1032,1033,1076,1140,1162]
  | 823 => [37,65,132,261,327,371,433,538,679,727,799,832,839,843,959,1032,1033,1076,1162]
  | 829 => [37,132,217,240,371,433,727,799,832,839,843,1115,1140,1162]
  | 830 => [37,132,217,245,371,433,727,799,832,839,843,1140,1162]
  | 831 => [37,132,217,261,371,433,727,799,832,839,843,1162]
  | 1016 => [132,240,241,281,371,433,714,757,799,839,843,1115,1140,1162]
  | 1017 => [132,240,280,281,371,431,433,701,714,777,799,839,843,1030,1110,1115,1140,1162]
  | 1018 => [132,241,245,281,371,433,714,757,799,839,843,1140,1162]
  | 1019 => [132,241,261,281,371,433,714,757,799,839,843,1162]
  | 1021 => [132,245,280,281,371,431,433,701,714,777,799,839,843,1030,1110,1140,1162]
  | 1022 => [132,261,280,281,371,431,433,701,714,777,799,839,843,1030,1110,1162]
  | _ => []
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def src1086 : List (List Nat) := [[371,843,260,440,3,293,857,867,1,871,296]]
theorem sourceIDs1086 : lowerHistorySourcePremises path1086 = src1086.map (List.map lowerHistoryBound) := by
  have hb : src1086.map (List.map lowerHistoryBound) = expected1086 := by
    simp only [src1086, expected1086, List.map_cons, List.map_nil, bound1, bound3, bound260, bound293, bound296, bound371, bound440, bound843, bound857, bound867, bound871]
  exact source1086.trans hb.symm
theorem length1086 : path1086.alternatives = (lowerHistorySourcePremises path1086).length := by
  rw [sourceIDs1086]
  rfl
theorem binding1086 : lowerHistoryPathBinding path1086 := by
  apply BindingIds19.pathBinding_from_ids path1086 src1086 [] recs1086 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1086 rfl records1086 rfl
  · intro r hr _
    simp only [recs1086, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise16)
  · intro r hr _
    simp only [recs1086, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1086] using witness286_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1086 recs1086 records1086 length1086 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
open BindingNumeric20
theorem op141 : lowerHistoryNecessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [bv132] := by
  decide +kernel
theorem op142 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = bv799 := by
  norm_num [bv799, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op143 : lowerHistoryPull (lowerHistoryH5) ([1],[]) false = bv1140 := by
  norm_num [bv1140, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op144 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH6)) ([1],[]) false = bv245 := by
  norm_num [bv245, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op145 : lowerHistoryPull (lowerHistoryH6) ([1],[]) false = bv1115 := by
  norm_num [bv1115, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op146 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7Mixed)) ([1],[]) false = bv240 := by
  norm_num [bv240, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op147 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = bv261 := by
  norm_num [bv261, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op148 : lowerHistoryNormalization ([1,3],[1]) true false = bv281 := by
  norm_num [bv281, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op149 : lowerHistoryNecessary ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[1]),true)⟩ ([1,3],[1]) = some [bv714] := by
  decide +kernel
theorem op150 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,3],[1]) true = bv241 := by
  norm_num [bv241, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op151 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,3],[1]) true = bv757 := by
  norm_num [bv757, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op152 : lowerHistoryPull (lowerHistoryHN) ([1,3],[1]) true = bv281 := by
  norm_num [bv281, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def path1087 : LowerHistoryPath := ⟨.initial,1,[2],([1],[]),false,[(([3],[1]),true)],([2,1,3],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩
noncomputable def raw1087 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv281,bv714,bv241,bv757,bv281],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv281,bv714,bv241,bv757,bv281],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv281,bv714,bv241,bv757,bv281]]
noncomputable def expected1087 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv281,bv714,bv241,bv757],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv281,bv714,bv241,bv757],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv281,bv714,bv241,bv757]]
theorem structural1087 (ops : RootOps19.SourceOps) (b132 b240 b241 b245 b261 b281 b371 b433 b714 b757 b799 b839 b843 b1115 b1140 b1162 : CertBound)
    (h138 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h139 : ([] : List CertBound) = [])
    (h140 : ops.normalization ([1],[]) false false = b839)
    (h141 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h142 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = b799)
    (h143 : ops.pull (lowerHistoryH5) ([1],[]) false = b1140)
    (h144 : ops.pull ((lowerHistoryComplement lowerHistoryH6)) ([1],[]) false = b245)
    (h145 : ops.pull (lowerHistoryH6) ([1],[]) false = b1115)
    (h146 : ops.pull ((lowerHistoryComplement lowerHistoryH7Mixed)) ([1],[]) false = b240)
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = b261)
    (h148 : ops.normalization ([1,3],[1]) true false = b281)
    (h149 : ops.necessary ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[1]),true)⟩ ([1,3],[1]) = some [b714])
    (h150 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,3],[1]) true = b241)
    (h151 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,3],[1]) true = b757)
    (h152 : ops.pull (lowerHistoryHN) ([1,3],[1]) true = b281)
    : RootOps19.eval ops path1087 = ([[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b281,b714,b241,b757,b281],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b281,b714,b241,b757,b281],[b371,b843,b433,b1162,b839,b132,b799,b261,b281,b714,b241,b757,b281]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1087, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h151, h152, hc0, hf0, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1087 : lowerHistorySourcePremises path1087 = raw1087.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1087 RootOps19.actualOps bv132 bv240 bv241 bv245 bv261 bv281 bv371 bv433 bv714 bv757 bv799 bv839 bv843 bv1115 bv1140 bv1162 op138 op139 op140 op141 op142 op143 op144 op145 op146 op147 op148 op149 op150 op151 op152
theorem dedup1087 : raw1087.map List.eraseDups = expected1087 := by
  decide +kernel
theorem source1087 : lowerHistorySourcePremises path1087 = expected1087 := (rawSource1087).trans (dedup1087)
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def src1087 : List (List Nat) := [[371,843,433,1162,839,132,799,1140,245,281,714,241,757],[371,843,433,1162,839,132,799,1140,1115,240,281,714,241,757],[371,843,433,1162,839,132,799,261,281,714,241,757]]
theorem sourceIDs1087 : lowerHistorySourcePremises path1087 = src1087.map (List.map lowerHistoryBound) := by
  have hb : src1087.map (List.map lowerHistoryBound) = expected1087 := by
    simp only [src1087, expected1087, List.map_cons, List.map_nil, bound132, bound240, bound241, bound245, bound261, bound281, bound371, bound433, bound714, bound757, bound799, bound839, bound843, bound1115, bound1140, bound1162]
  exact source1087.trans hb.symm
theorem length1087 : path1087.alternatives = (lowerHistorySourcePremises path1087).length := by
  rw [sourceIDs1087]
  rfl
theorem binding1087 : lowerHistoryPathBinding path1087 := by
  apply BindingIds19.pathBinding_from_ids path1087 src1087 [] recs1087 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1087 rfl records1087 rfl
  · intro r hr _
    simp only [recs1087, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1018)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1016)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1019)
  · intro r hr _
    simp only [recs1087, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockWids, path1087] using witness410_projection
    · simpa only [blockWids, path1087] using witness410_projection
    · simpa only [blockWids, path1087] using witness410_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1087 recs1087 records1087 length1087 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
open BindingNumeric20
theorem op153 : lowerHistoryPull (lowerHistoryH2) ([1,3],[1]) true = bv1110 := by
  norm_num [bv1110, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op154 : lowerHistoryNormalization ([1,3,1],[1]) true true = bv431 := by
  norm_num [bv431, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op155 : lowerHistoryNecessary ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,3,1],[1]) = some [bv701] := by
  decide +kernel
theorem op156 : lowerHistoryPull (lowerHistoryH7) ([1,3,1],[1]) true = bv777 := by
  norm_num [bv777, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op157 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,3,1],[1]) true = bv1030 := by
  norm_num [bv1030, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op158 : lowerHistoryPull (lowerHistoryHN) ([1,3,1],[1]) true = bv280 := by
  norm_num [bv280, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op159 : lowerHistoryNormalization ([1,3],[1]) false false = bv832 := by
  norm_num [bv832, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op160 : lowerHistoryNecessary ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([1,3],[1]) = some [bv37] := by
  decide +kernel
theorem op161 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,3],[1]) false = bv727 := by
  norm_num [bv727, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op162 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,3],[1]) false = bv217 := by
  norm_num [bv217, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op163 : lowerHistoryPull (lowerHistoryHN) ([1,3],[1]) false = bv832 := by
  norm_num [bv832, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op164 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,3],[1]) false = bv727 := by
  norm_num [bv727, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def path1088 : LowerHistoryPath := ⟨.initial,2,[2],([1],[]),false,[(([3],[1]),true),(([],[1]),false)],([2,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩
noncomputable def raw1088 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv281,bv714,bv1110,bv431,bv701,bv777,bv1030,bv280],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv281,bv714,bv1110,bv431,bv701,bv777,bv1030,bv280],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv281,bv714,bv1110,bv431,bv701,bv777,bv1030,bv280]]
noncomputable def expected1088 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv281,bv714,bv1110,bv431,bv701,bv777,bv1030,bv280],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv281,bv714,bv1110,bv431,bv701,bv777,bv1030,bv280],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv281,bv714,bv1110,bv431,bv701,bv777,bv1030,bv280]]
theorem structural1088 (ops : RootOps19.SourceOps) (b132 b240 b245 b261 b280 b281 b371 b431 b433 b701 b714 b777 b799 b839 b843 b1030 b1110 b1115 b1140 b1162 : CertBound)
    (h138 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h139 : ([] : List CertBound) = [])
    (h140 : ops.normalization ([1],[]) false false = b839)
    (h141 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h142 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = b799)
    (h143 : ops.pull (lowerHistoryH5) ([1],[]) false = b1140)
    (h144 : ops.pull ((lowerHistoryComplement lowerHistoryH6)) ([1],[]) false = b245)
    (h145 : ops.pull (lowerHistoryH6) ([1],[]) false = b1115)
    (h146 : ops.pull ((lowerHistoryComplement lowerHistoryH7Mixed)) ([1],[]) false = b240)
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = b261)
    (h148 : ops.normalization ([1,3],[1]) true false = b281)
    (h149 : ops.necessary ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[1]),true)⟩ ([1,3],[1]) = some [b714])
    (h153 : ops.pull (lowerHistoryH2) ([1,3],[1]) true = b1110)
    (h154 : ops.normalization ([1,3,1],[1]) true true = b431)
    (h155 : ops.necessary ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,3,1],[1]) = some [b701])
    (h156 : ops.pull (lowerHistoryH7) ([1,3,1],[1]) true = b777)
    (h157 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,3,1],[1]) true = b1030)
    (h158 : ops.pull (lowerHistoryHN) ([1,3,1],[1]) true = b280)
    : RootOps19.eval ops path1088 = ([[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b281,b714,b1110,b431,b701,b777,b1030,b280],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b281,b714,b1110,b431,b701,b777,b1030,b280],[b371,b843,b433,b1162,b839,b132,b799,b261,b281,b714,b1110,b431,b701,b777,b1030,b280]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[1]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1088, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h153, h154, h155, h156, h157, h158, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1088 : lowerHistorySourcePremises path1088 = raw1088.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1088 RootOps19.actualOps bv132 bv240 bv245 bv261 bv280 bv281 bv371 bv431 bv433 bv701 bv714 bv777 bv799 bv839 bv843 bv1030 bv1110 bv1115 bv1140 bv1162 op138 op139 op140 op141 op142 op143 op144 op145 op146 op147 op148 op149 op153 op154 op155 op156 op157 op158
theorem dedup1088 : raw1088.map List.eraseDups = expected1088 := by
  decide +kernel
theorem source1088 : lowerHistorySourcePremises path1088 = expected1088 := (rawSource1088).trans (dedup1088)
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def src1088 : List (List Nat) := [[371,843,433,1162,839,132,799,1140,245,281,714,1110,431,701,777,1030,280],[371,843,433,1162,839,132,799,1140,1115,240,281,714,1110,431,701,777,1030,280],[371,843,433,1162,839,132,799,261,281,714,1110,431,701,777,1030,280]]
theorem sourceIDs1088 : lowerHistorySourcePremises path1088 = src1088.map (List.map lowerHistoryBound) := by
  have hb : src1088.map (List.map lowerHistoryBound) = expected1088 := by
    simp only [src1088, expected1088, List.map_cons, List.map_nil, bound132, bound240, bound245, bound261, bound280, bound281, bound371, bound431, bound433, bound701, bound714, bound777, bound799, bound839, bound843, bound1030, bound1110, bound1115, bound1140, bound1162]
  exact source1088.trans hb.symm
theorem length1088 : path1088.alternatives = (lowerHistorySourcePremises path1088).length := by
  rw [sourceIDs1088]
  rfl
theorem binding1088 : lowerHistoryPathBinding path1088 := by
  apply BindingIds19.pathBinding_from_ids path1088 src1088 [] recs1088 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1088 rfl records1088 rfl
  · intro r hr _
    simp only [recs1088, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1021)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1017)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1022)
  · intro r hr _
    simp only [recs1088, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockWids, path1088] using witness504_projection
    · simpa only [blockWids, path1088] using witness504_projection
    · simpa only [blockWids, path1088] using witness504_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1088 recs1088 records1088 length1088 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def path1089 : LowerHistoryPath := ⟨.initial,3,[2],([1],[]),false,[(([3],[1]),false)],([2,1,3],[3,1,3,1]),(false,true),false,4,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩
noncomputable def raw1089 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv727,bv217,bv832],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv727,bv217,bv832],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv727,bv217,bv832]]
noncomputable def expected1089 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv727,bv217],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv727,bv217],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv727,bv217]]
theorem structural1089 (ops : RootOps19.SourceOps) (b37 b132 b217 b240 b245 b261 b371 b433 b727 b799 b832 b839 b843 b1115 b1140 b1162 : CertBound)
    (h138 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h139 : ([] : List CertBound) = [])
    (h140 : ops.normalization ([1],[]) false false = b839)
    (h141 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h142 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = b799)
    (h143 : ops.pull (lowerHistoryH5) ([1],[]) false = b1140)
    (h144 : ops.pull ((lowerHistoryComplement lowerHistoryH6)) ([1],[]) false = b245)
    (h145 : ops.pull (lowerHistoryH6) ([1],[]) false = b1115)
    (h146 : ops.pull ((lowerHistoryComplement lowerHistoryH7Mixed)) ([1],[]) false = b240)
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = b261)
    (h159 : ops.normalization ([1,3],[1]) false false = b832)
    (h160 : ops.necessary ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([1,3],[1]) = some [b37])
    (h161 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,3],[1]) false = b727)
    (h162 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,3],[1]) false = b217)
    (h163 : ops.pull (lowerHistoryHN) ([1,3],[1]) false = b832)
    : RootOps19.eval ops path1089 = ([[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b727,b217,b832],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b727,b217,b832],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b727,b217,b832]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1089, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h159, h160, h161, h162, h163, hc0, hf0, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1089 : lowerHistorySourcePremises path1089 = raw1089.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1089 RootOps19.actualOps bv37 bv132 bv217 bv240 bv245 bv261 bv371 bv433 bv727 bv799 bv832 bv839 bv843 bv1115 bv1140 bv1162 op138 op139 op140 op141 op142 op143 op144 op145 op146 op147 op159 op160 op161 op162 op163
theorem dedup1089 : raw1089.map List.eraseDups = expected1089 := by
  decide +kernel
theorem source1089 : lowerHistorySourcePremises path1089 = expected1089 := (rawSource1089).trans (dedup1089)
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def src1089 : List (List Nat) := [[371,843,433,1162,839,132,799,1140,245,832,37,727,217],[371,843,433,1162,839,132,799,1140,1115,240,832,37,727,217],[371,843,433,1162,839,132,799,261,832,37,727,217]]
theorem sourceIDs1089 : lowerHistorySourcePremises path1089 = src1089.map (List.map lowerHistoryBound) := by
  have hb : src1089.map (List.map lowerHistoryBound) = expected1089 := by
    simp only [src1089, expected1089, List.map_cons, List.map_nil, bound37, bound132, bound217, bound240, bound245, bound261, bound371, bound433, bound727, bound799, bound832, bound839, bound843, bound1115, bound1140, bound1162]
  exact source1089.trans hb.symm
theorem length1089 : path1089.alternatives = (lowerHistorySourcePremises path1089).length := by
  rw [sourceIDs1089]
  rfl
theorem binding1089 : lowerHistoryPathBinding path1089 := by
  apply BindingIds19.pathBinding_from_ids path1089 src1089 [] recs1089 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1089 rfl records1089 rfl
  · intro r hr _
    simp only [recs1089, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise830)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise829)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise831)
  · intro r hr _
    simp only [recs1089, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockWids, path1089] using witness405_projection
    · simpa only [blockWids, path1089] using witness405_projection
    · simpa only [blockWids, path1089] using witness405_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1089 recs1089 records1089 length1089 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
open BindingNumeric20
theorem op165 : lowerHistoryPull (lowerHistoryH5) ([1,3],[1]) false = bv1076 := by
  norm_num [bv1076, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op166 : lowerHistoryPull (lowerHistoryH6) ([1,3],[1]) false = bv1033 := by
  norm_num [bv1033, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op167 : lowerHistoryPull (lowerHistoryH7Mixed) ([1,3],[1]) false = bv1032 := by
  norm_num [bv1032, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op168 : lowerHistoryNormalization ([1,3,3],[1]) true true = bv327 := by
  norm_num [bv327, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op169 : lowerHistoryNecessary ⟨⟨([2,1,3,3],[3,1,3,1]),(true,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,3,3],[1]) = some [bv538] := by
  decide +kernel
theorem op170 : lowerHistoryPull (lowerHistoryH7) ([1,3,3],[1]) true = bv679 := by
  norm_num [bv679, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op171 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,3,3],[1]) true = bv959 := by
  norm_num [bv959, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op172 : lowerHistoryPull (lowerHistoryHN) ([1,3,3],[1]) true = bv65 := by
  norm_num [bv65, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def path1090 : LowerHistoryPath := ⟨.initial,4,[2],([1],[]),false,[(([3],[1]),false),(([3],[]),true)],([2,1,3,3],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩
noncomputable def raw1090 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv727,bv1076,bv1033,bv1032,bv327,bv538,bv679,bv959,bv65],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv727,bv1076,bv1033,bv1032,bv327,bv538,bv679,bv959,bv65],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv727,bv1076,bv1033,bv1032,bv327,bv538,bv679,bv959,bv65]]
noncomputable def expected1090 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv727,bv1076,bv1033,bv1032,bv327,bv538,bv679,bv959,bv65],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv727,bv1076,bv1033,bv1032,bv327,bv538,bv679,bv959,bv65],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv727,bv1076,bv1033,bv1032,bv327,bv538,bv679,bv959,bv65]]
theorem structural1090 (ops : RootOps19.SourceOps) (b37 b65 b132 b240 b245 b261 b327 b371 b433 b538 b679 b727 b799 b832 b839 b843 b959 b1032 b1033 b1076 b1115 b1140 b1162 : CertBound)
    (h138 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h139 : ([] : List CertBound) = [])
    (h140 : ops.normalization ([1],[]) false false = b839)
    (h141 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h142 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = b799)
    (h143 : ops.pull (lowerHistoryH5) ([1],[]) false = b1140)
    (h144 : ops.pull ((lowerHistoryComplement lowerHistoryH6)) ([1],[]) false = b245)
    (h145 : ops.pull (lowerHistoryH6) ([1],[]) false = b1115)
    (h146 : ops.pull ((lowerHistoryComplement lowerHistoryH7Mixed)) ([1],[]) false = b240)
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = b261)
    (h159 : ops.normalization ([1,3],[1]) false false = b832)
    (h160 : ops.necessary ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([1,3],[1]) = some [b37])
    (h164 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,3],[1]) false = b727)
    (h165 : ops.pull (lowerHistoryH5) ([1,3],[1]) false = b1076)
    (h166 : ops.pull (lowerHistoryH6) ([1,3],[1]) false = b1033)
    (h167 : ops.pull (lowerHistoryH7Mixed) ([1,3],[1]) false = b1032)
    (h168 : ops.normalization ([1,3,3],[1]) true true = b327)
    (h169 : ops.necessary ⟨⟨([2,1,3,3],[3,1,3,1]),(true,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,3,3],[1]) = some [b538])
    (h170 : ops.pull (lowerHistoryH7) ([1,3,3],[1]) true = b679)
    (h171 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,3,3],[1]) true = b959)
    (h172 : ops.pull (lowerHistoryHN) ([1,3,3],[1]) true = b65)
    : RootOps19.eval ops path1090 = ([[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b727,b1076,b1033,b1032,b327,b538,b679,b959,b65],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b727,b1076,b1033,b1032,b327,b538,b679,b959,b65],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b727,b1076,b1033,b1032,b327,b538,b679,b959,b65]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,lowerHistoryH7Mixed]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1090, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h159, h160, h164, h165, h166, h167, h168, h169, h170, h171, h172, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1090 : lowerHistorySourcePremises path1090 = raw1090.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1090 RootOps19.actualOps bv37 bv65 bv132 bv240 bv245 bv261 bv327 bv371 bv433 bv538 bv679 bv727 bv799 bv832 bv839 bv843 bv959 bv1032 bv1033 bv1076 bv1115 bv1140 bv1162 op138 op139 op140 op141 op142 op143 op144 op145 op146 op147 op159 op160 op164 op165 op166 op167 op168 op169 op170 op171 op172
theorem dedup1090 : raw1090.map List.eraseDups = expected1090 := by
  decide +kernel
theorem source1090 : lowerHistorySourcePremises path1090 = expected1090 := (rawSource1090).trans (dedup1090)
end M7ContinueSep17.Initial20260918.B1085_1090

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1085_1090
noncomputable def src1090 : List (List Nat) := [[371,843,433,1162,839,132,799,1140,245,832,37,727,1076,1033,1032,327,538,679,959,65],[371,843,433,1162,839,132,799,1140,1115,240,832,37,727,1076,1033,1032,327,538,679,959,65],[371,843,433,1162,839,132,799,261,832,37,727,1076,1033,1032,327,538,679,959,65]]
theorem sourceIDs1090 : lowerHistorySourcePremises path1090 = src1090.map (List.map lowerHistoryBound) := by
  have hb : src1090.map (List.map lowerHistoryBound) = expected1090 := by
    simp only [src1090, expected1090, List.map_cons, List.map_nil, bound37, bound65, bound132, bound240, bound245, bound261, bound327, bound371, bound433, bound538, bound679, bound727, bound799, bound832, bound839, bound843, bound959, bound1032, bound1033, bound1076, bound1115, bound1140, bound1162]
  exact source1090.trans hb.symm
theorem length1090 : path1090.alternatives = (lowerHistorySourcePremises path1090).length := by
  rw [sourceIDs1090]
  rfl
theorem binding1090 : lowerHistoryPathBinding path1090 := by
  apply BindingIds19.pathBinding_from_ids path1090 src1090 [] recs1090 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1090 rfl records1090 rfl
  · intro r hr _
    simp only [recs1090, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise822)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise821)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise823)
  · intro r hr _
    simp only [recs1090, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockWids, path1090] using witness476_projection
    · simpa only [blockWids, path1090] using witness476_projection
    · simpa only [blockWids, path1090] using witness476_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1090 recs1090 records1090 length1090 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1085_1090

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
namespace M7ContinueSep17.Initial20260918.B1085_1090
theorem _root_.solution : lowerHistoryBindingBatch 1085 1090 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1085]? = some M7ContinueSep17.Initial20260918.B1085_1090.path1086 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 89 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1086
  · have hl : lowerHistoryPaths[1086]? = some M7ContinueSep17.Initial20260918.B1085_1090.path1087 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 0 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1087
  · have hl : lowerHistoryPaths[1087]? = some M7ContinueSep17.Initial20260918.B1085_1090.path1088 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 1 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1088
  · have hl : lowerHistoryPaths[1088]? = some M7ContinueSep17.Initial20260918.B1085_1090.path1089 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 2 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1089
  · have hl : lowerHistoryPaths[1089]? = some M7ContinueSep17.Initial20260918.B1085_1090.path1090 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 3 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1090
end M7ContinueSep17.Initial20260918.B1085_1090

#print axioms solution
