-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1405_1410
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T07:24:32.532288+00:00
-- url     : https://prove2.me/submissions/92ed39dc-bf26-4ff2-bcc9-4745ce5d594e

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
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def bv47 : CertBound := ⟨true,false,⟨⟨(-286369/4976303),(218632/4976303),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(241/409),(-1/409),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv55 : CertBound := ⟨true,false,⟨⟨(-73/2227),(0),(0),(28/2227)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv60 : CertBound := ⟨true,false,⟨⟨(-239829/10233574),(546631/30700722),(0),(0)⟩,⟨(181/314),(1/942),(0),(0)⟩,⟨(823/1417),(-1/1417),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv80 : CertBound := ⟨true,false,⟨⟨(-637821/73117414),(1456879/219352242),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(1508/2593),(-1/2593),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv98 : CertBound := ⟨true,false,⟨⟨(-15/4454),(0),(0),(37/13362)⟩,⟨(97/170),(0),(0),(1/510)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv105 : CertBound := ⟨true,false,⟨⟨(-47/25670),(0),(0),(91/77010)⟩,⟨(97/170),(0),(0),(1/510)⟩,⟨(881/1510),(0),(0),(-1/1510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv113 : CertBound := ⟨true,false,⟨⟨(-857/1426195),(0),(0),(612/1426195)⟩,⟨(2187/3778),(0),(0),(1/3778)⟩,⟨(881/1510),(0),(0),(-1/1510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv125 : CertBound := ⟨true,false,⟨⟨(157/56212),(1831/84318),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv128 : CertBound := ⟨true,false,⟨⟨(7984397450/1928575040639),(77186750/1928575040639),(0),(0)⟩,⟨(83983/144766),(-1/144766),(0),(0)⟩,⟨(32145/55393),(1/55393),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv132 : CertBound := ⟨true,false,⟨⟨(133/21164),(324/5291),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv163 : CertBound := ⟨true,false,⟨⟨(2064383/127104900),(453127/127104900),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(129/218),(-1/654),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv181 : CertBound := ⟨true,false,⟨⟨(5059465150/178709345581),(141895750/536128036743),(0),(0)⟩,⟨(12212/21061),(-1/21061),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv192 : CertBound := ⟨true,false,⟨⟨(224300/6577379),(-50/533301),(0),(0)⟩,⟨(1741/3013),(-1/3013),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv202 : CertBound := ⟨true,false,⟨⟨(5983/141700),(279/28340),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv314 : CertBound := ⟨true,true,⟨⟨(-45/697),(0),(0),(14/697)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(53/82),(0),(0),(-1/82)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv315 : CertBound := ⟨true,true,⟨⟨(-249/4454),(0),(0),(65/4454)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv354 : CertBound := ⟨true,true,⟨⟨(-15/4454),(0),(0),(37/13362)⟩,⟨(97/170),(0),(0),(1/510)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv367 : CertBound := ⟨true,true,⟨⟨(-857/1426195),(0),(0),(612/1426195)⟩,⟨(2187/3778),(0),(0),(1/3778)⟩,⟨(881/1510),(0),(0),(-1/1510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv433 : CertBound := ⟨true,true,⟨⟨(729/1024),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv447 : CertBound := ⟨false,false,⟨⟨(-3/10),(0),(0),(1/10)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv458 : CertBound := ⟨false,false,⟨⟨(-73/2227),(0),(0),(28/2227)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv459 : CertBound := ⟨false,false,⟨⟨(-37/1394),(0),(0),(27/1394)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(53/82),(0),(0),(-1/82)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv462 : CertBound := ⟨false,false,⟨⟨(-15/4454),(0),(0),(37/13362)⟩,⟨(97/170),(0),(0),(1/510)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv479 : CertBound := ⟨false,false,⟨⟨(104588/76988509),(614405/230965527),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(5606/9661),(-1/9661),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv485 : CertBound := ⟨false,false,⟨⟨(2430659/1401830422),(2446169/1401830422),(0),(0)⟩,⟨(42053/72551),(1/217653),(0),(0)⟩,⟨(5606/9661),(-1/9661),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv504 : CertBound := ⟨false,false,⟨⟨(3135/868621),(18128/2605863),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(823/1417),(-1/1417),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv520 : CertBound := ⟨false,false,⟨⟨(43525316000/8026237234461),(7470775000/72236135110149),(0),(0)⟩,⟨(3861/6661),(1/6661),(0),(0)⟩,⟨(83983/144766),(-1/144766),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv531 : CertBound := ⟨false,false,⟨⟨(537281850/75656770783),(-167837550/75656770783),(0),(0)⟩,⟨(14655/25261),(1/25261),(0),(0)⟩,⟨(10195/17566),(-1/17566),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv544 : CertBound := ⟨false,false,⟨⟨(6809/749593),(13695/749593),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(823/1417),(-1/1417),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv559 : CertBound := ⟨false,false,⟨⟨(1253/113206),(2433/113206),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv569 : CertBound := ⟨false,false,⟨⟨(529485/43595422),(264913/21797711),(0),(0)⟩,⟨(17733/30766),(1/30766),(0),(0)⟩,⟨(823/1417),(-1/1417),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv601 : CertBound := ⟨false,false,⟨⟨(567805/28339588),(394237/28339588),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(7895/13393),(-1/13393),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv604 : CertBound := ⟨false,false,⟨⟨(101/4922),(857/14766),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv630 : CertBound := ⟨false,false,⟨⟨(19283/735839),(34958/735839),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv656 : CertBound := ⟨false,false,⟨⟨(18725456000/495401285871),(278689000/495401285871),(0),(0)⟩,⟨(181/314),(1/942),(0),(0)⟩,⟨(12212/21061),(-1/21061),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv676 : CertBound := ⟨false,false,⟨⟨(26243850/542022569),(-8189050/542022569),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(1508/2593),(-1/2593),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv681 : CertBound := ⟨false,false,⟨⟨(259000/4995117),(-623500/464545881),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(241/409),(-1/409),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(66/179),(-1/537),(0),(0)⟩⟩⟩
noncomputable def bv839 : CertBound := ⟨false,false,⟨⟨(9/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv840 : CertBound := ⟨false,false,⟨⟨(21/23),(-32/69),(0),(0)⟩,⟨(0),(1/3),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv917 : CertBound := ⟨false,true,⟨⟨(197562/221867363),(385771/665602089),(0),(0)⟩,⟨(14655/25261),(1/25261),(0),(0)⟩,⟨(10195/17566),(-1/17566),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv948 : CertBound := ⟨false,true,⟨⟨(7984397450/1928575040639),(77186750/1928575040639),(0),(0)⟩,⟨(83983/144766),(-1/144766),(0),(0)⟩,⟨(32145/55393),(1/55393),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv953 : CertBound := ⟨false,true,⟨⟨(28991/4768527),(18866/4768527),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(1508/2593),(-1/2593),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv955 : CertBound := ⟨false,true,⟨⟨(6429432250/1042313969489),(-415410250/1042313969489),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(83983/144766),(-1/144766),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1027 : CertBound := ⟨false,true,⟨⟨(5059465150/178709345581),(141895750/536128036743),(0),(0)⟩,⟨(12212/21061),(-1/21061),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1038 : CertBound := ⟨false,true,⟨⟨(224300/6577379),(-50/533301),(0),(0)⟩,⟨(1741/3013),(-1/3013),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1052 : CertBound := ⟨false,true,⟨⟨(5983/141700),(279/28340),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1053 : CertBound := ⟨false,true,⟨⟨(11178076500/261719550079),(-806937500/261719550079),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(12212/21061),(-1/21061),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1062 : CertBound := ⟨false,true,⟨⟨(9250/188623),(-500/188623),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1162 : CertBound := ⟨false,true,⟨⟨(225/289),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [bv371,bv843,bv433,bv1162] := by
  decide +kernel
theorem op1 : ([] : List CertBound) = [] := by
  decide +kernel
theorem op2 : lowerHistoryNormalization ([1],[]) false false = bv839 := by
  norm_num [bv839, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op3 : lowerHistoryNecessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [bv132] := by
  decide +kernel
theorem op4 : lowerHistoryNormalization ([1,1],[]) false false = bv447 := by
  norm_num [bv447, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op5 : lowerHistoryNecessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [bv125] := by
  decide +kernel
theorem op6 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = bv1052 := by
  norm_num [bv1052, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op7 : lowerHistoryPull (lowerHistoryH7) ([1,1],[]) false = bv202 := by
  norm_num [bv202, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op8 : lowerHistoryPull (lowerHistoryH9) ([1,1],[]) false = bv840 := by
  norm_num [bv840, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op9 : lowerHistoryNormalization ([1,1,2],[]) true true = bv314 := by
  norm_num [bv314, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op10 : lowerHistoryNecessary ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [bv604] := by
  decide +kernel
theorem op11 : lowerHistoryPull (lowerHistoryH2) ([1,1,2],[]) true = bv1038 := by
  norm_num [bv1038, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
open BindingNumeric20
theorem op12 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = bv192 := by
  norm_num [bv192, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op13 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = bv681 := by
  norm_num [bv681, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op14 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = bv601 := by
  norm_num [bv601, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op15 : lowerHistoryPull (lowerHistoryH23) ([1,1,2],[]) true = bv1062 := by
  norm_num [bv1062, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op16 : lowerHistoryNormalization ([1,1,2,1],[]) true true = bv315 := by
  norm_num [bv315, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op17 : lowerHistoryNecessary ⟨⟨([3,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [bv559] := by
  decide +kernel
theorem op18 : lowerHistoryNormalization ([1,1,2,1],[1]) false false = bv458 := by
  norm_num [bv458, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op19 : lowerHistoryNecessary ⟨⟨([3,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2,1],[1]) = some [bv60] := by
  decide +kernel
theorem op20 : lowerHistoryNormalization ([1,1,2,1,1],[1]) false false = bv462 := by
  norm_num [bv462, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op21 : lowerHistoryNecessary ⟨⟨([3,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,2,1,1],[1]) = some [bv80] := by
  decide +kernel
theorem op52 : lowerHistoryNormalization ([1,1,2,1,1,1],[1]) true false = bv105 := by
  norm_num [bv105, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op53 : lowerHistoryNecessary ⟨⟨([3,1,1,2,1,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,2,1,1,1],[1]) = some [bv504] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
open BindingNumeric20
theorem op54 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,2,1,1,1],[1]) true = bv128 := by
  norm_num [bv128, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op55 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,2,1,1,1],[1]) true = bv520 := by
  norm_num [bv520, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op56 : lowerHistoryPull (lowerHistoryHN) ([1,1,2,1,1,1],[1]) true = bv105 := by
  norm_num [bv105, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op57 : lowerHistoryPull (lowerHistoryH2) ([1,1,2,1,1,1],[1]) true = bv948 := by
  norm_num [bv948, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op58 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2,1,1,1],[1]) true = bv128 := by
  norm_num [bv128, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op59 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2,1,1,1],[1]) true = bv520 := by
  norm_num [bv520, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op60 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2,1,1,1],[1]) true = bv485 := by
  norm_num [bv485, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op61 : lowerHistoryPull (lowerHistoryH23) ([1,1,2,1,1,1],[1]) true = bv955 := by
  norm_num [bv955, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op62 : lowerHistoryNormalization ([1,1,2,1,1,1,1],[1]) true true = bv367 := by
  norm_num [bv367, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op63 : lowerHistoryNecessary ⟨⟨([3,1,1,2,1,1,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1,1,1],[1]) = some [bv479] := by
  decide +kernel
theorem op64 : lowerHistoryPull (lowerHistoryH7) ([1,1,2,1,1,1,1],[1]) true = bv531 := by
  norm_num [bv531, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op65 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1,1,1],[1]) true = bv917 := by
  norm_num [bv917, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def path1406 : LowerHistoryPath := ⟨.initial,320,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,1,2,1,1,1],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,4⟩
noncomputable def raw1406 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv105],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv105],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv105],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv105]]
noncomputable def expected1406 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520]]
theorem structural1406 (ops : RootOps19.SourceOps) (b60 b80 b105 b125 b128 b132 b192 b202 b314 b315 b371 b433 b447 b458 b462 b504 b520 b559 b601 b604 b681 b839 b840 b843 b1038 b1052 b1062 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h7 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h8 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h9 : ops.normalization ([1,1,2],[]) true true = b314)
    (h10 : ops.necessary ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h11 : ops.pull (lowerHistoryH2) ([1,1,2],[]) true = b1038)
    (h12 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = b192)
    (h13 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = b681)
    (h14 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = b601)
    (h15 : ops.pull (lowerHistoryH23) ([1,1,2],[]) true = b1062)
    (h16 : ops.normalization ([1,1,2,1],[]) true true = b315)
    (h17 : ops.necessary ⟨⟨([3,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [b559])
    (h18 : ops.normalization ([1,1,2,1],[1]) false false = b458)
    (h19 : ops.necessary ⟨⟨([3,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2,1],[1]) = some [b60])
    (h20 : ops.normalization ([1,1,2,1,1],[1]) false false = b462)
    (h21 : ops.necessary ⟨⟨([3,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,2,1,1],[1]) = some [b80])
    (h52 : ops.normalization ([1,1,2,1,1,1],[1]) true false = b105)
    (h53 : ops.necessary ⟨⟨([3,1,1,2,1,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,2,1,1,1],[1]) = some [b504])
    (h54 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,2,1,1,1],[1]) true = b128)
    (h55 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,2,1,1,1],[1]) true = b520)
    (h56 : ops.pull (lowerHistoryHN) ([1,1,2,1,1,1],[1]) true = b105)
    : RootOps19.eval ops path1406 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b105],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b105],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b105],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b105]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1406, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h52, h53, h54, h55, h56, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1406 : lowerHistorySourcePremises path1406 = raw1406.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1406 RootOps19.actualOps bv60 bv80 bv105 bv125 bv128 bv132 bv192 bv202 bv314 bv315 bv371 bv433 bv447 bv458 bv462 bv504 bv520 bv559 bv601 bv604 bv681 bv839 bv840 bv843 bv1038 bv1052 bv1062 bv1162 op0 op1 op2 op3 op4 op5 op6 op7 op8 op9 op10 op11 op12 op13 op14 op15 op16 op17 op18 op19 op20 op21 op52 op53 op54 op55 op56
theorem dedup1406 : raw1406.map List.eraseDups = expected1406 := by
  decide +kernel
theorem source1406 : lowerHistorySourcePremises path1406 = expected1406 := (rawSource1406).trans (dedup1406)
end M7ContinueSep17.Initial20260918.B1405_1410

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
namespace M7ContinueSep17.Initial20260918.B1405_1410
theorem bound47 : lowerHistoryBound 47 = bv47 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[46]? = some bv47 := Eq.refl (some bv47)
  exact (BoundCompact16.global_to_chunk1 46 (by decide)).trans hl
theorem bound55 : lowerHistoryBound 55 = bv55 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[54]? = some bv55 := Eq.refl (some bv55)
  exact (BoundCompact16.global_to_chunk1 54 (by decide)).trans hl
theorem bound60 : lowerHistoryBound 60 = bv60 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[59]? = some bv60 := Eq.refl (some bv60)
  exact (BoundCompact16.global_to_chunk1 59 (by decide)).trans hl
theorem bound80 : lowerHistoryBound 80 = bv80 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[79]? = some bv80 := Eq.refl (some bv80)
  exact (BoundCompact16.global_to_chunk1 79 (by decide)).trans hl
theorem bound98 : lowerHistoryBound 98 = bv98 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[97]? = some bv98 := Eq.refl (some bv98)
  exact (BoundCompact16.global_to_chunk1 97 (by decide)).trans hl
theorem bound105 : lowerHistoryBound 105 = bv105 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[104]? = some bv105 := Eq.refl (some bv105)
  exact (BoundCompact16.global_to_chunk1 104 (by decide)).trans hl
theorem bound113 : lowerHistoryBound 113 = bv113 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[112]? = some bv113 := Eq.refl (some bv113)
  exact (BoundCompact16.global_to_chunk1 112 (by decide)).trans hl
theorem bound125 : lowerHistoryBound 125 = bv125 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[124]? = some bv125 := Eq.refl (some bv125)
  exact (BoundCompact16.global_to_chunk1 124 (by decide)).trans hl
theorem bound128 : lowerHistoryBound 128 = bv128 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[127]? = some bv128 := Eq.refl (some bv128)
  exact (BoundCompact16.global_to_chunk1 127 (by decide)).trans hl
theorem bound132 : lowerHistoryBound 132 = bv132 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[131]? = some bv132 := Eq.refl (some bv132)
  exact (BoundCompact16.global_to_chunk1 131 (by decide)).trans hl
theorem bound163 : lowerHistoryBound 163 = bv163 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[162]? = some bv163 := Eq.refl (some bv163)
  exact (BoundCompact16.global_to_chunk1 162 (by decide)).trans hl
theorem bound181 : lowerHistoryBound 181 = bv181 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[180]? = some bv181 := Eq.refl (some bv181)
  exact (BoundCompact16.global_to_chunk1 180 (by decide)).trans hl
theorem bound192 : lowerHistoryBound 192 = bv192 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[191]? = some bv192 := Eq.refl (some bv192)
  exact (BoundCompact16.global_to_chunk1 191 (by decide)).trans hl
theorem bound202 : lowerHistoryBound 202 = bv202 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[1]? = some bv202 := Eq.refl (some bv202)
  exact (BoundCompact16.global_to_chunk2 1 (by decide)).trans hl
theorem bound314 : lowerHistoryBound 314 = bv314 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[113]? = some bv314 := Eq.refl (some bv314)
  exact (BoundCompact16.global_to_chunk2 113 (by decide)).trans hl
theorem bound315 : lowerHistoryBound 315 = bv315 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[114]? = some bv315 := Eq.refl (some bv315)
  exact (BoundCompact16.global_to_chunk2 114 (by decide)).trans hl
theorem bound354 : lowerHistoryBound 354 = bv354 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[153]? = some bv354 := Eq.refl (some bv354)
  exact (BoundCompact16.global_to_chunk2 153 (by decide)).trans hl
theorem bound367 : lowerHistoryBound 367 = bv367 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[166]? = some bv367 := Eq.refl (some bv367)
  exact (BoundCompact16.global_to_chunk2 166 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound433 : lowerHistoryBound 433 = bv433 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[32]? = some bv433 := Eq.refl (some bv433)
  exact (BoundCompact16.global_to_chunk3 32 (by decide)).trans hl
theorem bound447 : lowerHistoryBound 447 = bv447 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[46]? = some bv447 := Eq.refl (some bv447)
  exact (BoundCompact16.global_to_chunk3 46 (by decide)).trans hl
theorem bound458 : lowerHistoryBound 458 = bv458 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[57]? = some bv458 := Eq.refl (some bv458)
  exact (BoundCompact16.global_to_chunk3 57 (by decide)).trans hl
theorem bound459 : lowerHistoryBound 459 = bv459 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[58]? = some bv459 := Eq.refl (some bv459)
  exact (BoundCompact16.global_to_chunk3 58 (by decide)).trans hl
theorem bound462 : lowerHistoryBound 462 = bv462 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[61]? = some bv462 := Eq.refl (some bv462)
  exact (BoundCompact16.global_to_chunk3 61 (by decide)).trans hl
theorem bound479 : lowerHistoryBound 479 = bv479 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[78]? = some bv479 := Eq.refl (some bv479)
  exact (BoundCompact16.global_to_chunk3 78 (by decide)).trans hl
theorem bound485 : lowerHistoryBound 485 = bv485 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[84]? = some bv485 := Eq.refl (some bv485)
  exact (BoundCompact16.global_to_chunk3 84 (by decide)).trans hl
theorem bound504 : lowerHistoryBound 504 = bv504 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[103]? = some bv504 := Eq.refl (some bv504)
  exact (BoundCompact16.global_to_chunk3 103 (by decide)).trans hl
theorem bound520 : lowerHistoryBound 520 = bv520 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[119]? = some bv520 := Eq.refl (some bv520)
  exact (BoundCompact16.global_to_chunk3 119 (by decide)).trans hl
theorem bound531 : lowerHistoryBound 531 = bv531 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[130]? = some bv531 := Eq.refl (some bv531)
  exact (BoundCompact16.global_to_chunk3 130 (by decide)).trans hl
theorem bound544 : lowerHistoryBound 544 = bv544 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[143]? = some bv544 := Eq.refl (some bv544)
  exact (BoundCompact16.global_to_chunk3 143 (by decide)).trans hl
theorem bound559 : lowerHistoryBound 559 = bv559 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[158]? = some bv559 := Eq.refl (some bv559)
  exact (BoundCompact16.global_to_chunk3 158 (by decide)).trans hl
theorem bound569 : lowerHistoryBound 569 = bv569 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[168]? = some bv569 := Eq.refl (some bv569)
  exact (BoundCompact16.global_to_chunk3 168 (by decide)).trans hl
theorem bound601 : lowerHistoryBound 601 = bv601 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[0]? = some bv601 := Eq.refl (some bv601)
  exact (BoundCompact16.global_to_chunk4 0 (by decide)).trans hl
theorem bound604 : lowerHistoryBound 604 = bv604 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[3]? = some bv604 := Eq.refl (some bv604)
  exact (BoundCompact16.global_to_chunk4 3 (by decide)).trans hl
theorem bound630 : lowerHistoryBound 630 = bv630 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[29]? = some bv630 := Eq.refl (some bv630)
  exact (BoundCompact16.global_to_chunk4 29 (by decide)).trans hl
theorem bound656 : lowerHistoryBound 656 = bv656 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[55]? = some bv656 := Eq.refl (some bv656)
  exact (BoundCompact16.global_to_chunk4 55 (by decide)).trans hl
theorem bound676 : lowerHistoryBound 676 = bv676 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[75]? = some bv676 := Eq.refl (some bv676)
  exact (BoundCompact16.global_to_chunk4 75 (by decide)).trans hl
theorem bound681 : lowerHistoryBound 681 = bv681 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[80]? = some bv681 := Eq.refl (some bv681)
  exact (BoundCompact16.global_to_chunk4 80 (by decide)).trans hl
theorem bound839 : lowerHistoryBound 839 = bv839 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[38]? = some bv839 := Eq.refl (some bv839)
  exact (BoundCompact16.global_to_chunk5 38 (by decide)).trans hl
theorem bound840 : lowerHistoryBound 840 = bv840 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[39]? = some bv840 := Eq.refl (some bv840)
  exact (BoundCompact16.global_to_chunk5 39 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound917 : lowerHistoryBound 917 = bv917 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[116]? = some bv917 := Eq.refl (some bv917)
  exact (BoundCompact16.global_to_chunk5 116 (by decide)).trans hl
theorem bound948 : lowerHistoryBound 948 = bv948 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[147]? = some bv948 := Eq.refl (some bv948)
  exact (BoundCompact16.global_to_chunk5 147 (by decide)).trans hl
theorem bound953 : lowerHistoryBound 953 = bv953 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[152]? = some bv953 := Eq.refl (some bv953)
  exact (BoundCompact16.global_to_chunk5 152 (by decide)).trans hl
theorem bound955 : lowerHistoryBound 955 = bv955 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[154]? = some bv955 := Eq.refl (some bv955)
  exact (BoundCompact16.global_to_chunk5 154 (by decide)).trans hl
theorem bound1027 : lowerHistoryBound 1027 = bv1027 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[26]? = some bv1027 := Eq.refl (some bv1027)
  exact (BoundCompact16.global_to_chunk6 26).trans hl
theorem bound1038 : lowerHistoryBound 1038 = bv1038 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[37]? = some bv1038 := Eq.refl (some bv1038)
  exact (BoundCompact16.global_to_chunk6 37).trans hl
theorem bound1052 : lowerHistoryBound 1052 = bv1052 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[51]? = some bv1052 := Eq.refl (some bv1052)
  exact (BoundCompact16.global_to_chunk6 51).trans hl
theorem bound1053 : lowerHistoryBound 1053 = bv1053 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[52]? = some bv1053 := Eq.refl (some bv1053)
  exact (BoundCompact16.global_to_chunk6 52).trans hl
theorem bound1062 : lowerHistoryBound 1062 = bv1062 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[61]? = some bv1062 := Eq.refl (some bv1062)
  exact (BoundCompact16.global_to_chunk6 61).trans hl
theorem bound1162 : lowerHistoryBound 1162 = bv1162 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[161]? = some bv1162 := Eq.refl (some bv1162)
  exact (BoundCompact16.global_to_chunk6 161).trans hl
end M7ContinueSep17.Initial20260918.B1405_1410

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

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def recs1406 : List LowerHistoryRecord := [⟨.initial,320,0,(-1),false,960,359⟩,⟨.initial,320,1,(-1),false,958,359⟩,⟨.initial,320,2,(-1),false,959,359⟩,⟨.initial,320,3,(-1),false,957,359⟩]
theorem records1406 : lowerHistoryRecordsFor (⟨.initial,320,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,1,2,1,1,1],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,4⟩ : LowerHistoryPath) = recs1406 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 320)) = recs1406
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1407 : List LowerHistoryRecord := [⟨.initial,321,0,(-1),false,956,438⟩,⟨.initial,321,1,(-1),false,952,438⟩,⟨.initial,321,2,(-1),false,954,438⟩,⟨.initial,321,3,(-1),false,950,438⟩,⟨.initial,321,4,(-1),false,955,438⟩,⟨.initial,321,5,(-1),false,951,438⟩,⟨.initial,321,6,(-1),false,953,438⟩,⟨.initial,321,7,(-1),false,949,438⟩]
theorem records1407 : lowerHistoryRecordsFor (⟨.initial,321,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,1,2,1,1,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,8⟩ : LowerHistoryPath) = recs1407 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 321)) = recs1407
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1408 : List LowerHistoryRecord := [⟨.initial,322,0,(-1),false,913,505⟩,⟨.initial,322,1,(-1),false,911,376⟩,⟨.initial,322,2,(-1),false,912,505⟩,⟨.initial,322,3,(-1),false,910,376⟩]
theorem records1408 : lowerHistoryRecordsFor (⟨.initial,322,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),false)],([3,1,1,2,1],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,4⟩ : LowerHistoryPath) = recs1408 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 322)) = recs1408
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1409 : List LowerHistoryRecord := [⟨.initial,323,0,(-1),false,909,470⟩,⟨.initial,323,1,(-1),false,905,470⟩,⟨.initial,323,2,(-1),false,907,470⟩,⟨.initial,323,3,(-1),false,903,470⟩,⟨.initial,323,4,(-1),false,908,470⟩,⟨.initial,323,5,(-1),false,904,470⟩,⟨.initial,323,6,(-1),false,906,470⟩,⟨.initial,323,7,(-1),false,902,470⟩]
theorem records1409 : lowerHistoryRecordsFor (⟨.initial,323,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,1,2,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,8⟩ : LowerHistoryPath) = recs1409 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 323)) = recs1409
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1410 : List LowerHistoryRecord := [⟨.initial,324,0,(-1),false,897,511⟩,⟨.initial,324,1,(-1),false,895,335⟩]
theorem records1410 : lowerHistoryRecordsFor (⟨.initial,324,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true)],([3,1,1,2],[3,1,3,1]),(true,true),false,2,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1410 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 324)) = recs1410
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
end M7ContinueSep17.Initial20260918.B1405_1410

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
namespace M7ContinueSep17.Initial20260918.B1405_1410
theorem premise895 : lowerHistoryPremises[894]? = some ([47,125,132,163,202,314,371,433,447,459,604,839,840,843,1162] : List Nat) := by
  have hg : lowerHistoryPremises[894]? = lowerHistoryPremises05[94]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 94 (by decide)
  exact hg.trans (by rfl)
theorem premise897 : lowerHistoryPremises[896]? = some ([47,125,132,163,314,371,433,447,459,604,839,843,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[896]? = lowerHistoryPremises05[96]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 96 (by decide)
  exact hg.trans (by rfl)
theorem premise902 : lowerHistoryPremises[901]? = some ([55,98,125,132,181,192,202,314,315,354,371,433,447,544,559,569,601,604,630,656,676,681,839,840,843,953,1053,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[901]? = lowerHistoryPremises05[101]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 101 (by decide)
  exact hg.trans (by rfl)
theorem premise903 : lowerHistoryPremises[902]? = some ([55,98,125,132,181,192,314,315,354,371,433,447,544,559,569,601,604,630,656,676,681,839,843,953,1052,1053,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[902]? = lowerHistoryPremises05[102]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 102 (by decide)
  exact hg.trans (by rfl)
theorem premise904 : lowerHistoryPremises[903]? = some ([55,98,125,132,181,202,314,315,354,371,433,447,544,559,569,604,630,656,676,839,840,843,953,1038,1053,1162] : List Nat) := by
  have hg : lowerHistoryPremises[903]? = lowerHistoryPremises05[103]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 103 (by decide)
  exact hg.trans (by rfl)
theorem premise905 : lowerHistoryPremises[904]? = some ([55,98,125,132,181,314,315,354,371,433,447,544,559,569,604,630,656,676,839,843,953,1038,1052,1053,1162] : List Nat) := by
  have hg : lowerHistoryPremises[904]? = lowerHistoryPremises05[104]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 104 (by decide)
  exact hg.trans (by rfl)
theorem premise906 : lowerHistoryPremises[905]? = some ([55,98,125,132,192,202,314,315,354,371,433,447,544,559,601,604,630,676,681,839,840,843,953,1027,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[905]? = lowerHistoryPremises05[105]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 105 (by decide)
  exact hg.trans (by rfl)
theorem premise907 : lowerHistoryPremises[906]? = some ([55,98,125,132,192,314,315,354,371,433,447,544,559,601,604,630,676,681,839,843,953,1027,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[906]? = lowerHistoryPremises05[106]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 106 (by decide)
  exact hg.trans (by rfl)
theorem premise908 : lowerHistoryPremises[907]? = some ([55,98,125,132,202,314,315,354,371,433,447,544,559,604,630,676,839,840,843,953,1027,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[907]? = lowerHistoryPremises05[107]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 107 (by decide)
  exact hg.trans (by rfl)
theorem premise909 : lowerHistoryPremises[908]? = some ([55,98,125,132,314,315,354,371,433,447,544,559,604,630,676,839,843,953,1027,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[908]? = lowerHistoryPremises05[108]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 108 (by decide)
  exact hg.trans (by rfl)
theorem premise910 : lowerHistoryPremises[909]? = some ([55,125,132,181,192,202,314,315,371,433,447,559,601,604,630,656,681,839,840,843,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[909]? = lowerHistoryPremises05[109]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 109 (by decide)
  exact hg.trans (by rfl)
theorem premise911 : lowerHistoryPremises[910]? = some ([55,125,132,181,192,314,315,371,433,447,559,601,604,630,656,681,839,843,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[910]? = lowerHistoryPremises05[110]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 110 (by decide)
  exact hg.trans (by rfl)
theorem premise912 : lowerHistoryPremises[911]? = some ([55,125,132,181,202,314,315,371,433,447,559,604,630,656,839,840,843,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[911]? = lowerHistoryPremises05[111]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 111 (by decide)
  exact hg.trans (by rfl)
theorem premise913 : lowerHistoryPremises[912]? = some ([55,125,132,181,314,315,371,433,447,559,604,630,656,839,843,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[912]? = lowerHistoryPremises05[112]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 112 (by decide)
  exact hg.trans (by rfl)
theorem premise949 : lowerHistoryPremises[948]? = some ([60,80,105,113,125,128,132,192,202,314,315,367,371,433,447,458,462,479,485,504,520,531,559,601,604,681,839,840,843,917,955,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[948]? = lowerHistoryPremises05[148]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 148 (by decide)
  exact hg.trans (by rfl)
theorem premise950 : lowerHistoryPremises[949]? = some ([60,80,105,113,125,128,132,192,314,315,367,371,433,447,458,462,479,485,504,520,531,559,601,604,681,839,843,917,955,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[949]? = lowerHistoryPremises05[149]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 149 (by decide)
  exact hg.trans (by rfl)
theorem premise951 : lowerHistoryPremises[950]? = some ([60,80,105,113,125,128,132,202,314,315,367,371,433,447,458,462,479,485,504,520,531,559,604,839,840,843,917,955,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[950]? = lowerHistoryPremises05[150]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 150 (by decide)
  exact hg.trans (by rfl)
theorem premise952 : lowerHistoryPremises[951]? = some ([60,80,105,113,125,128,132,314,315,367,371,433,447,458,462,479,485,504,520,531,559,604,839,843,917,955,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[951]? = lowerHistoryPremises05[151]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 151 (by decide)
  exact hg.trans (by rfl)
theorem premise953 : lowerHistoryPremises[952]? = some ([60,80,105,113,125,132,192,202,314,315,367,371,433,447,458,462,479,504,531,559,601,604,681,839,840,843,917,948,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[952]? = lowerHistoryPremises05[152]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 152 (by decide)
  exact hg.trans (by rfl)
theorem premise954 : lowerHistoryPremises[953]? = some ([60,80,105,113,125,132,192,314,315,367,371,433,447,458,462,479,504,531,559,601,604,681,839,843,917,948,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[953]? = lowerHistoryPremises05[153]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 153 (by decide)
  exact hg.trans (by rfl)
theorem premise955 : lowerHistoryPremises[954]? = some ([60,80,105,113,125,132,202,314,315,367,371,433,447,458,462,479,504,531,559,604,839,840,843,917,948,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[954]? = lowerHistoryPremises05[154]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 154 (by decide)
  exact hg.trans (by rfl)
theorem premise956 : lowerHistoryPremises[955]? = some ([60,80,105,113,125,132,314,315,367,371,433,447,458,462,479,504,531,559,604,839,843,917,948,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[955]? = lowerHistoryPremises05[155]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 155 (by decide)
  exact hg.trans (by rfl)
theorem premise957 : lowerHistoryPremises[956]? = some ([60,80,105,125,128,132,192,202,314,315,371,433,447,458,462,504,520,559,601,604,681,839,840,843,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[956]? = lowerHistoryPremises05[156]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 156 (by decide)
  exact hg.trans (by rfl)
theorem premise958 : lowerHistoryPremises[957]? = some ([60,80,105,125,128,132,192,314,315,371,433,447,458,462,504,520,559,601,604,681,839,843,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[957]? = lowerHistoryPremises05[157]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 157 (by decide)
  exact hg.trans (by rfl)
theorem premise959 : lowerHistoryPremises[958]? = some ([60,80,105,125,128,132,202,314,315,371,433,447,458,462,504,520,559,604,839,840,843,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[958]? = lowerHistoryPremises05[158]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 158 (by decide)
  exact hg.trans (by rfl)
theorem premise960 : lowerHistoryPremises[959]? = some ([60,80,105,125,128,132,314,315,371,433,447,458,462,504,520,559,604,839,843,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[959]? = lowerHistoryPremises05[159]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 159 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1405_1410
theorem witness335_projection : (lowerHistoryWitness 335).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 335).upperBound = lowerHistoryBound 459 ∧ (lowerHistoryWitness 335).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[134]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 459, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 459, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[334]? = lowerHistoryWitnesses02[134]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 134 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness359_projection : (lowerHistoryWitness 359).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 359).upperBound = lowerHistoryBound 520 ∧ (lowerHistoryWitness 359).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[158]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 520, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 520, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[358]? = lowerHistoryWitnesses02[158]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 158 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness376_projection : (lowerHistoryWitness 376).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 376).upperBound = lowerHistoryBound 601 ∧ (lowerHistoryWitness 376).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[175]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 601, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 601, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[375]? = lowerHistoryWitnesses02[175]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 175 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness438_projection : (lowerHistoryWitness 438).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 438).upperBound = lowerHistoryBound 917 ∧ (lowerHistoryWitness 438).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[37]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 917, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 917, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[437]? = lowerHistoryWitnesses03[37]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 37 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness470_projection : (lowerHistoryWitness 470).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 470).upperBound = lowerHistoryBound 953 ∧ (lowerHistoryWitness 470).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[69]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 953, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 953, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[469]? = lowerHistoryWitnesses03[69]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 69 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness505_projection : (lowerHistoryWitness 505).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 505).upperBound = lowerHistoryBound 1038 ∧ (lowerHistoryWitness 505).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[104]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 1038, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 1038, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[504]? = lowerHistoryWitnesses03[104]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 104 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness511_projection : (lowerHistoryWitness 511).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 511).upperBound = lowerHistoryBound 1052 ∧ (lowerHistoryWitness 511).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[110]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 1052, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 1052, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[510]? = lowerHistoryWitnesses03[110]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 110 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 335 => (433,459)
  | 359 => (433,520)
  | 376 => (433,601)
  | 438 => (433,917)
  | 470 => (433,953)
  | 505 => (433,1038)
  | 511 => (433,1052)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 895 => [47,125,132,163,202,314,371,433,447,459,604,839,840,843,1162]
  | 897 => [47,125,132,163,314,371,433,447,459,604,839,843,1052,1162]
  | 902 => [55,98,125,132,181,192,202,314,315,354,371,433,447,544,559,569,601,604,630,656,676,681,839,840,843,953,1053,1062,1162]
  | 903 => [55,98,125,132,181,192,314,315,354,371,433,447,544,559,569,601,604,630,656,676,681,839,843,953,1052,1053,1062,1162]
  | 904 => [55,98,125,132,181,202,314,315,354,371,433,447,544,559,569,604,630,656,676,839,840,843,953,1038,1053,1162]
  | 905 => [55,98,125,132,181,314,315,354,371,433,447,544,559,569,604,630,656,676,839,843,953,1038,1052,1053,1162]
  | 906 => [55,98,125,132,192,202,314,315,354,371,433,447,544,559,601,604,630,676,681,839,840,843,953,1027,1062,1162]
  | 907 => [55,98,125,132,192,314,315,354,371,433,447,544,559,601,604,630,676,681,839,843,953,1027,1052,1062,1162]
  | 908 => [55,98,125,132,202,314,315,354,371,433,447,544,559,604,630,676,839,840,843,953,1027,1038,1162]
  | 909 => [55,98,125,132,314,315,354,371,433,447,544,559,604,630,676,839,843,953,1027,1038,1052,1162]
  | 910 => [55,125,132,181,192,202,314,315,371,433,447,559,601,604,630,656,681,839,840,843,1062,1162]
  | 911 => [55,125,132,181,192,314,315,371,433,447,559,601,604,630,656,681,839,843,1052,1062,1162]
  | 912 => [55,125,132,181,202,314,315,371,433,447,559,604,630,656,839,840,843,1038,1162]
  | 913 => [55,125,132,181,314,315,371,433,447,559,604,630,656,839,843,1038,1052,1162]
  | 949 => [60,80,105,113,125,128,132,192,202,314,315,367,371,433,447,458,462,479,485,504,520,531,559,601,604,681,839,840,843,917,955,1062,1162]
  | 950 => [60,80,105,113,125,128,132,192,314,315,367,371,433,447,458,462,479,485,504,520,531,559,601,604,681,839,843,917,955,1052,1062,1162]
  | 951 => [60,80,105,113,125,128,132,202,314,315,367,371,433,447,458,462,479,485,504,520,531,559,604,839,840,843,917,955,1038,1162]
  | 952 => [60,80,105,113,125,128,132,314,315,367,371,433,447,458,462,479,485,504,520,531,559,604,839,843,917,955,1038,1052,1162]
  | 953 => [60,80,105,113,125,132,192,202,314,315,367,371,433,447,458,462,479,504,531,559,601,604,681,839,840,843,917,948,1062,1162]
  | 954 => [60,80,105,113,125,132,192,314,315,367,371,433,447,458,462,479,504,531,559,601,604,681,839,843,917,948,1052,1062,1162]
  | 955 => [60,80,105,113,125,132,202,314,315,367,371,433,447,458,462,479,504,531,559,604,839,840,843,917,948,1038,1162]
  | 956 => [60,80,105,113,125,132,314,315,367,371,433,447,458,462,479,504,531,559,604,839,843,917,948,1038,1052,1162]
  | 957 => [60,80,105,125,128,132,192,202,314,315,371,433,447,458,462,504,520,559,601,604,681,839,840,843,1062,1162]
  | 958 => [60,80,105,125,128,132,192,314,315,371,433,447,458,462,504,520,559,601,604,681,839,843,1052,1062,1162]
  | 959 => [60,80,105,125,128,132,202,314,315,371,433,447,458,462,504,520,559,604,839,840,843,1038,1162]
  | 960 => [60,80,105,125,128,132,314,315,371,433,447,458,462,504,520,559,604,839,843,1038,1052,1162]
  | _ => []
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def src1406 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,105,504,128,520],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,128,520],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,105,504,128,520],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,128,520]]
theorem sourceIDs1406 : lowerHistorySourcePremises path1406 = src1406.map (List.map lowerHistoryBound) := by
  have hb : src1406.map (List.map lowerHistoryBound) = expected1406 := by
    simp only [src1406, expected1406, List.map_cons, List.map_nil, bound60, bound80, bound105, bound125, bound128, bound132, bound192, bound202, bound314, bound315, bound371, bound433, bound447, bound458, bound462, bound504, bound520, bound559, bound601, bound604, bound681, bound839, bound840, bound843, bound1038, bound1052, bound1062, bound1162]
  exact source1406.trans hb.symm
theorem length1406 : path1406.alternatives = (lowerHistorySourcePremises path1406).length := by
  rw [sourceIDs1406]
  rfl
theorem binding1406 : lowerHistoryPathBinding path1406 := by
  apply BindingIds19.pathBinding_from_ids path1406 src1406 [] recs1406 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1406 rfl records1406 rfl
  · intro r hr _
    simp only [recs1406, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise960)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise958)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise959)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise957)
  · intro r hr _
    simp only [recs1406, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1406] using witness359_projection
    · simpa only [blockWids, path1406] using witness359_projection
    · simpa only [blockWids, path1406] using witness359_projection
    · simpa only [blockWids, path1406] using witness359_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1406 recs1406 records1406 length1406 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
open BindingNumeric20
theorem op66 : lowerHistoryPull (lowerHistoryHN) ([1,1,2,1,1,1,1],[1]) true = bv113 := by
  norm_num [bv113, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op67 : lowerHistoryNormalization ([1,1,2,1],[1]) true false = bv55 := by
  norm_num [bv55, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op68 : lowerHistoryNecessary ⟨⟨([3,1,1,2,1],[3,1,3,1]),(false,true)⟩,true,true,some (true,([1],[]),false)⟩ ([1,1,2,1],[1]) = some [bv630] := by
  decide +kernel
theorem op69 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,2,1],[1]) true = bv181 := by
  norm_num [bv181, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op70 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,2,1],[1]) true = bv656 := by
  norm_num [bv656, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op71 : lowerHistoryPull (lowerHistoryHN) ([1,1,2,1],[1]) true = bv55 := by
  norm_num [bv55, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op72 : lowerHistoryPull (lowerHistoryH2) ([1,1,2,1],[1]) true = bv1027 := by
  norm_num [bv1027, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op73 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2,1],[1]) true = bv181 := by
  norm_num [bv181, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op74 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2,1],[1]) true = bv656 := by
  norm_num [bv656, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op75 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2,1],[1]) true = bv569 := by
  norm_num [bv569, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op76 : lowerHistoryPull (lowerHistoryH23) ([1,1,2,1],[1]) true = bv1053 := by
  norm_num [bv1053, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op77 : lowerHistoryNormalization ([1,1,2,1,1],[1]) true true = bv354 := by
  norm_num [bv354, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def path1407 : LowerHistoryPath := ⟨.initial,321,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,1,2,1,1,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,8⟩
noncomputable def raw1407 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113]]
noncomputable def expected1407 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113]]
theorem structural1407 (ops : RootOps19.SourceOps) (b60 b80 b105 b113 b125 b128 b132 b192 b202 b314 b315 b367 b371 b433 b447 b458 b462 b479 b485 b504 b520 b531 b559 b601 b604 b681 b839 b840 b843 b917 b948 b955 b1038 b1052 b1062 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h7 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h8 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h9 : ops.normalization ([1,1,2],[]) true true = b314)
    (h10 : ops.necessary ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h11 : ops.pull (lowerHistoryH2) ([1,1,2],[]) true = b1038)
    (h12 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = b192)
    (h13 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = b681)
    (h14 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = b601)
    (h15 : ops.pull (lowerHistoryH23) ([1,1,2],[]) true = b1062)
    (h16 : ops.normalization ([1,1,2,1],[]) true true = b315)
    (h17 : ops.necessary ⟨⟨([3,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [b559])
    (h18 : ops.normalization ([1,1,2,1],[1]) false false = b458)
    (h19 : ops.necessary ⟨⟨([3,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2,1],[1]) = some [b60])
    (h20 : ops.normalization ([1,1,2,1,1],[1]) false false = b462)
    (h21 : ops.necessary ⟨⟨([3,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,2,1,1],[1]) = some [b80])
    (h52 : ops.normalization ([1,1,2,1,1,1],[1]) true false = b105)
    (h53 : ops.necessary ⟨⟨([3,1,1,2,1,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,2,1,1,1],[1]) = some [b504])
    (h57 : ops.pull (lowerHistoryH2) ([1,1,2,1,1,1],[1]) true = b948)
    (h58 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2,1,1,1],[1]) true = b128)
    (h59 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2,1,1,1],[1]) true = b520)
    (h60 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2,1,1,1],[1]) true = b485)
    (h61 : ops.pull (lowerHistoryH23) ([1,1,2,1,1,1],[1]) true = b955)
    (h62 : ops.normalization ([1,1,2,1,1,1,1],[1]) true true = b367)
    (h63 : ops.necessary ⟨⟨([3,1,1,2,1,1,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1,1,1],[1]) = some [b479])
    (h64 : ops.pull (lowerHistoryH7) ([1,1,2,1,1,1,1],[1]) true = b531)
    (h65 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1,1,1],[1]) true = b917)
    (h66 : ops.pull (lowerHistoryHN) ([1,1,2,1,1,1,1],[1]) true = b113)
    : RootOps19.eval ops path1407 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b948,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b485,b955,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b948,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b485,b955,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b948,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b485,b955,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b948,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b485,b955,b367,b479,b531,b917,b113]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc6 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf6 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1407, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h52, h53, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hf0, hf1, hf2, hf3, hf4, hf5, hf6, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1407 : lowerHistorySourcePremises path1407 = raw1407.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1407 RootOps19.actualOps bv60 bv80 bv105 bv113 bv125 bv128 bv132 bv192 bv202 bv314 bv315 bv367 bv371 bv433 bv447 bv458 bv462 bv479 bv485 bv504 bv520 bv531 bv559 bv601 bv604 bv681 bv839 bv840 bv843 bv917 bv948 bv955 bv1038 bv1052 bv1062 bv1162 op0 op1 op2 op3 op4 op5 op6 op7 op8 op9 op10 op11 op12 op13 op14 op15 op16 op17 op18 op19 op20 op21 op52 op53 op57 op58 op59 op60 op61 op62 op63 op64 op65 op66
theorem dedup1407 : raw1407.map List.eraseDups = expected1407 := by
  decide +kernel
theorem source1407 : lowerHistorySourcePremises path1407 = expected1407 := (rawSource1407).trans (dedup1407)
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def src1407 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,105,504,948,367,479,531,917,113],[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,105,504,128,520,485,955,367,479,531,917,113],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,948,367,479,531,917,113],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,128,520,485,955,367,479,531,917,113],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,105,504,948,367,479,531,917,113],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,105,504,128,520,485,955,367,479,531,917,113],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,948,367,479,531,917,113],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,128,520,485,955,367,479,531,917,113]]
theorem sourceIDs1407 : lowerHistorySourcePremises path1407 = src1407.map (List.map lowerHistoryBound) := by
  have hb : src1407.map (List.map lowerHistoryBound) = expected1407 := by
    simp only [src1407, expected1407, List.map_cons, List.map_nil, bound60, bound80, bound105, bound113, bound125, bound128, bound132, bound192, bound202, bound314, bound315, bound367, bound371, bound433, bound447, bound458, bound462, bound479, bound485, bound504, bound520, bound531, bound559, bound601, bound604, bound681, bound839, bound840, bound843, bound917, bound948, bound955, bound1038, bound1052, bound1062, bound1162]
  exact source1407.trans hb.symm
theorem length1407 : path1407.alternatives = (lowerHistorySourcePremises path1407).length := by
  rw [sourceIDs1407]
  rfl
theorem binding1407 : lowerHistoryPathBinding path1407 := by
  apply BindingIds19.pathBinding_from_ids path1407 src1407 [] recs1407 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1407 rfl records1407 rfl
  · intro r hr _
    simp only [recs1407, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise956)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise952)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise954)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise950)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise955)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise951)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise953)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise949)
  · intro r hr _
    simp only [recs1407, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1407] using witness438_projection
    · simpa only [blockWids, path1407] using witness438_projection
    · simpa only [blockWids, path1407] using witness438_projection
    · simpa only [blockWids, path1407] using witness438_projection
    · simpa only [blockWids, path1407] using witness438_projection
    · simpa only [blockWids, path1407] using witness438_projection
    · simpa only [blockWids, path1407] using witness438_projection
    · simpa only [blockWids, path1407] using witness438_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1407 recs1407 records1407 length1407 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def path1408 : LowerHistoryPath := ⟨.initial,322,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),false)],([3,1,1,2,1],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,4⟩
noncomputable def raw1408 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv181,bv656,bv55],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv181,bv656,bv55],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv181,bv656,bv55],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv181,bv656,bv55]]
noncomputable def expected1408 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv181,bv656],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv181,bv656],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv181,bv656],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv181,bv656]]
theorem structural1408 (ops : RootOps19.SourceOps) (b55 b125 b132 b181 b192 b202 b314 b315 b371 b433 b447 b559 b601 b604 b630 b656 b681 b839 b840 b843 b1038 b1052 b1062 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h7 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h8 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h9 : ops.normalization ([1,1,2],[]) true true = b314)
    (h10 : ops.necessary ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h11 : ops.pull (lowerHistoryH2) ([1,1,2],[]) true = b1038)
    (h12 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = b192)
    (h13 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = b681)
    (h14 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = b601)
    (h15 : ops.pull (lowerHistoryH23) ([1,1,2],[]) true = b1062)
    (h16 : ops.normalization ([1,1,2,1],[]) true true = b315)
    (h17 : ops.necessary ⟨⟨([3,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [b559])
    (h67 : ops.normalization ([1,1,2,1],[1]) true false = b55)
    (h68 : ops.necessary ⟨⟨([3,1,1,2,1],[3,1,3,1]),(false,true)⟩,true,true,some (true,([1],[]),false)⟩ ([1,1,2,1],[1]) = some [b630])
    (h69 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,2,1],[1]) true = b181)
    (h70 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,2,1],[1]) true = b656)
    (h71 : ops.pull (lowerHistoryHN) ([1,1,2,1],[1]) true = b55)
    : RootOps19.eval ops path1408 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b55,b630,b181,b656,b55],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b55,b630,b181,b656,b55],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b55,b630,b181,b656,b55],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b55,b630,b181,b656,b55]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1408, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h67, h68, h69, h70, h71, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1408 : lowerHistorySourcePremises path1408 = raw1408.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1408 RootOps19.actualOps bv55 bv125 bv132 bv181 bv192 bv202 bv314 bv315 bv371 bv433 bv447 bv559 bv601 bv604 bv630 bv656 bv681 bv839 bv840 bv843 bv1038 bv1052 bv1062 bv1162 op0 op1 op2 op3 op4 op5 op6 op7 op8 op9 op10 op11 op12 op13 op14 op15 op16 op17 op67 op68 op69 op70 op71
theorem dedup1408 : raw1408.map List.eraseDups = expected1408 := by
  decide +kernel
theorem source1408 : lowerHistorySourcePremises path1408 = expected1408 := (rawSource1408).trans (dedup1408)
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def src1408 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,55,630,181,656],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,55,630,181,656],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,55,630,181,656],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,55,630,181,656]]
theorem sourceIDs1408 : lowerHistorySourcePremises path1408 = src1408.map (List.map lowerHistoryBound) := by
  have hb : src1408.map (List.map lowerHistoryBound) = expected1408 := by
    simp only [src1408, expected1408, List.map_cons, List.map_nil, bound55, bound125, bound132, bound181, bound192, bound202, bound314, bound315, bound371, bound433, bound447, bound559, bound601, bound604, bound630, bound656, bound681, bound839, bound840, bound843, bound1038, bound1052, bound1062, bound1162]
  exact source1408.trans hb.symm
theorem length1408 : path1408.alternatives = (lowerHistorySourcePremises path1408).length := by
  rw [sourceIDs1408]
  rfl
theorem binding1408 : lowerHistoryPathBinding path1408 := by
  apply BindingIds19.pathBinding_from_ids path1408 src1408 [] recs1408 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1408 rfl records1408 rfl
  · intro r hr _
    simp only [recs1408, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise913)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise911)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise912)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise910)
  · intro r hr _
    simp only [recs1408, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1408] using witness505_projection
    · simpa only [blockWids, path1408] using witness376_projection
    · simpa only [blockWids, path1408] using witness505_projection
    · simpa only [blockWids, path1408] using witness376_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1408 recs1408 records1408 length1408 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
open BindingNumeric20
theorem op78 : lowerHistoryNecessary ⟨⟨([3,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1],[1]) = some [bv544] := by
  decide +kernel
theorem op79 : lowerHistoryPull (lowerHistoryH7) ([1,1,2,1,1],[1]) true = bv676 := by
  norm_num [bv676, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op80 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1],[1]) true = bv953 := by
  norm_num [bv953, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op81 : lowerHistoryPull (lowerHistoryHN) ([1,1,2,1,1],[1]) true = bv98 := by
  norm_num [bv98, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op82 : lowerHistoryNormalization ([1,1,2],[1]) false false = bv459 := by
  norm_num [bv459, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op83 : lowerHistoryNecessary ⟨⟨([3,1,1,2],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2],[1]) = some [bv47] := by
  decide +kernel
theorem op84 : lowerHistoryPull (lowerHistoryH7) ([1,1,2],[1]) false = bv163 := by
  norm_num [bv163, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op85 : lowerHistoryPull (lowerHistoryHN) ([1,1,2],[1]) false = bv459 := by
  norm_num [bv459, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def path1409 : LowerHistoryPath := ⟨.initial,323,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,1,2,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,8⟩
noncomputable def raw1409 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv1027,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv181,bv656,bv569,bv1053,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv1027,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv181,bv656,bv569,bv1053,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv1027,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv181,bv656,bv569,bv1053,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv1027,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv181,bv656,bv569,bv1053,bv354,bv544,bv676,bv953,bv98]]
noncomputable def expected1409 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv1027,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv181,bv656,bv569,bv1053,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv1027,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv181,bv656,bv569,bv1053,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv1027,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv55,bv630,bv181,bv656,bv569,bv1053,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv1027,bv354,bv544,bv676,bv953,bv98],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv55,bv630,bv181,bv656,bv569,bv1053,bv354,bv544,bv676,bv953,bv98]]
theorem structural1409 (ops : RootOps19.SourceOps) (b55 b98 b125 b132 b181 b192 b202 b314 b315 b354 b371 b433 b447 b544 b559 b569 b601 b604 b630 b656 b676 b681 b839 b840 b843 b953 b1027 b1038 b1052 b1053 b1062 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h7 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h8 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h9 : ops.normalization ([1,1,2],[]) true true = b314)
    (h10 : ops.necessary ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h11 : ops.pull (lowerHistoryH2) ([1,1,2],[]) true = b1038)
    (h12 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = b192)
    (h13 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = b681)
    (h14 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = b601)
    (h15 : ops.pull (lowerHistoryH23) ([1,1,2],[]) true = b1062)
    (h16 : ops.normalization ([1,1,2,1],[]) true true = b315)
    (h17 : ops.necessary ⟨⟨([3,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [b559])
    (h67 : ops.normalization ([1,1,2,1],[1]) true false = b55)
    (h68 : ops.necessary ⟨⟨([3,1,1,2,1],[3,1,3,1]),(false,true)⟩,true,true,some (true,([1],[]),false)⟩ ([1,1,2,1],[1]) = some [b630])
    (h72 : ops.pull (lowerHistoryH2) ([1,1,2,1],[1]) true = b1027)
    (h73 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2,1],[1]) true = b181)
    (h74 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2,1],[1]) true = b656)
    (h75 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2,1],[1]) true = b569)
    (h76 : ops.pull (lowerHistoryH23) ([1,1,2,1],[1]) true = b1053)
    (h77 : ops.normalization ([1,1,2,1,1],[1]) true true = b354)
    (h78 : ops.necessary ⟨⟨([3,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1],[1]) = some [b544])
    (h79 : ops.pull (lowerHistoryH7) ([1,1,2,1,1],[1]) true = b676)
    (h80 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1],[1]) true = b953)
    (h81 : ops.pull (lowerHistoryHN) ([1,1,2,1,1],[1]) true = b98)
    : RootOps19.eval ops path1409 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b55,b630,b1027,b354,b544,b676,b953,b98],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b55,b630,b181,b656,b569,b1053,b354,b544,b676,b953,b98],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b55,b630,b1027,b354,b544,b676,b953,b98],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b55,b630,b181,b656,b569,b1053,b354,b544,b676,b953,b98],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b55,b630,b1027,b354,b544,b676,b953,b98],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b55,b630,b181,b656,b569,b1053,b354,b544,b676,b953,b98],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b55,b630,b1027,b354,b544,b676,b953,b98],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b55,b630,b181,b656,b569,b1053,b354,b544,b676,b953,b98]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,2,1],[3,1,3,1]),(false,true)⟩,true,true,some (true,([1],[]),false)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1409, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h67, h68, h72, h73, h74, h75, h76, h77, h78, h79, h80, h81, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1409 : lowerHistorySourcePremises path1409 = raw1409.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1409 RootOps19.actualOps bv55 bv98 bv125 bv132 bv181 bv192 bv202 bv314 bv315 bv354 bv371 bv433 bv447 bv544 bv559 bv569 bv601 bv604 bv630 bv656 bv676 bv681 bv839 bv840 bv843 bv953 bv1027 bv1038 bv1052 bv1053 bv1062 bv1162 op0 op1 op2 op3 op4 op5 op6 op7 op8 op9 op10 op11 op12 op13 op14 op15 op16 op17 op67 op68 op72 op73 op74 op75 op76 op77 op78 op79 op80 op81
theorem dedup1409 : raw1409.map List.eraseDups = expected1409 := by
  decide +kernel
theorem source1409 : lowerHistorySourcePremises path1409 = expected1409 := (rawSource1409).trans (dedup1409)
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def src1409 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,55,630,1027,354,544,676,953,98],[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,55,630,181,656,569,1053,354,544,676,953,98],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,55,630,1027,354,544,676,953,98],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,55,630,181,656,569,1053,354,544,676,953,98],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,55,630,1027,354,544,676,953,98],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,55,630,181,656,569,1053,354,544,676,953,98],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,55,630,1027,354,544,676,953,98],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,55,630,181,656,569,1053,354,544,676,953,98]]
theorem sourceIDs1409 : lowerHistorySourcePremises path1409 = src1409.map (List.map lowerHistoryBound) := by
  have hb : src1409.map (List.map lowerHistoryBound) = expected1409 := by
    simp only [src1409, expected1409, List.map_cons, List.map_nil, bound55, bound98, bound125, bound132, bound181, bound192, bound202, bound314, bound315, bound354, bound371, bound433, bound447, bound544, bound559, bound569, bound601, bound604, bound630, bound656, bound676, bound681, bound839, bound840, bound843, bound953, bound1027, bound1038, bound1052, bound1053, bound1062, bound1162]
  exact source1409.trans hb.symm
theorem length1409 : path1409.alternatives = (lowerHistorySourcePremises path1409).length := by
  rw [sourceIDs1409]
  rfl
theorem binding1409 : lowerHistoryPathBinding path1409 := by
  apply BindingIds19.pathBinding_from_ids path1409 src1409 [] recs1409 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1409 rfl records1409 rfl
  · intro r hr _
    simp only [recs1409, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise909)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise905)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise907)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise903)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise908)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise904)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise906)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise902)
  · intro r hr _
    simp only [recs1409, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1409] using witness470_projection
    · simpa only [blockWids, path1409] using witness470_projection
    · simpa only [blockWids, path1409] using witness470_projection
    · simpa only [blockWids, path1409] using witness470_projection
    · simpa only [blockWids, path1409] using witness470_projection
    · simpa only [blockWids, path1409] using witness470_projection
    · simpa only [blockWids, path1409] using witness470_projection
    · simpa only [blockWids, path1409] using witness470_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1409 recs1409 records1409 length1409 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def path1410 : LowerHistoryPath := ⟨.initial,324,[3],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true)],([3,1,1,2],[3,1,3,1]),(true,true),false,2,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩
noncomputable def raw1410 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv459,bv47,bv163,bv459],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv459,bv47,bv163,bv459]]
noncomputable def expected1410 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv459,bv47,bv163],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv459,bv47,bv163]]
theorem structural1410 (ops : RootOps19.SourceOps) (b47 b125 b132 b163 b202 b314 b371 b433 b447 b459 b604 b839 b840 b843 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h7 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h8 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h9 : ops.normalization ([1,1,2],[]) true true = b314)
    (h10 : ops.necessary ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h82 : ops.normalization ([1,1,2],[1]) false false = b459)
    (h83 : ops.necessary ⟨⟨([3,1,1,2],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2],[1]) = some [b47])
    (h84 : ops.pull (lowerHistoryH7) ([1,1,2],[1]) false = b163)
    (h85 : ops.pull (lowerHistoryHN) ([1,1,2],[1]) false = b459)
    : RootOps19.eval ops path1410 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b459,b47,b163,b459],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b459,b47,b163,b459]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1410, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h82, h83, h84, h85, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1410 : lowerHistorySourcePremises path1410 = raw1410.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1410 RootOps19.actualOps bv47 bv125 bv132 bv163 bv202 bv314 bv371 bv433 bv447 bv459 bv604 bv839 bv840 bv843 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op6 op7 op8 op9 op10 op82 op83 op84 op85
theorem dedup1410 : raw1410.map List.eraseDups = expected1410 := by
  decide +kernel
theorem source1410 : lowerHistorySourcePremises path1410 = expected1410 := (rawSource1410).trans (dedup1410)
end M7ContinueSep17.Initial20260918.B1405_1410

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1405_1410
noncomputable def src1410 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,459,47,163],[371,843,433,1162,839,132,447,125,202,840,314,604,459,47,163]]
theorem sourceIDs1410 : lowerHistorySourcePremises path1410 = src1410.map (List.map lowerHistoryBound) := by
  have hb : src1410.map (List.map lowerHistoryBound) = expected1410 := by
    simp only [src1410, expected1410, List.map_cons, List.map_nil, bound47, bound125, bound132, bound163, bound202, bound314, bound371, bound433, bound447, bound459, bound604, bound839, bound840, bound843, bound1052, bound1162]
  exact source1410.trans hb.symm
theorem length1410 : path1410.alternatives = (lowerHistorySourcePremises path1410).length := by
  rw [sourceIDs1410]
  rfl
theorem binding1410 : lowerHistoryPathBinding path1410 := by
  apply BindingIds19.pathBinding_from_ids path1410 src1410 [] recs1410 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1410 rfl records1410 rfl
  · intro r hr _
    simp only [recs1410, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise897)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise895)
  · intro r hr _
    simp only [recs1410, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1410] using witness511_projection
    · simpa only [blockWids, path1410] using witness335_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1410 recs1410 records1410 length1410 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1405_1410

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
namespace M7ContinueSep17.Initial20260918.B1405_1410
theorem _root_.solution : lowerHistoryBindingBatch 1405 1410 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1405]? = some M7ContinueSep17.Initial20260918.B1405_1410.path1406 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 319 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1406
  · have hl : lowerHistoryPaths[1406]? = some M7ContinueSep17.Initial20260918.B1405_1410.path1407 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 320 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1407
  · have hl : lowerHistoryPaths[1407]? = some M7ContinueSep17.Initial20260918.B1405_1410.path1408 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 321 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1408
  · have hl : lowerHistoryPaths[1408]? = some M7ContinueSep17.Initial20260918.B1405_1410.path1409 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 322 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1409
  · have hl : lowerHistoryPaths[1409]? = some M7ContinueSep17.Initial20260918.B1405_1410.path1410 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 323 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1410
end M7ContinueSep17.Initial20260918.B1405_1410

#print axioms solution
