-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1390_1395
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T07:08:12.616916+00:00
-- url     : https://prove2.me/submissions/4bc53f55-cbc5-49ac-8760-7c98d7bb49d3

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
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def bv31 : CertBound := ⟨true,false,⟨⟨(-11/85),(0),(0),(8/255)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv56 : CertBound := ⟨true,false,⟨⟨(-169591/5270749),(388984/15812247),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(142/251),(-1/753),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv70 : CertBound := ⟨true,false,⟨⟨(-415417/30547726),(945823/91643178),(0),(0)⟩,⟨(897/1606),(1/1606),(0),(0)⟩,⟨(464/827),(-1/2481),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv107 : CertBound := ⟨true,false,⟨⟨(-123/71230),(0),(0),(329/213690)⟩,⟨(465/838),(0),(0),(1/838)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv108 : CertBound := ⟨true,false,⟨⟨(-183/109289),(0),(0),(304/327867)⟩,⟨(323/586),(0),(0),(1/586)⟩,⟨(419/746),(0),(0),(-1/2238)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv125 : CertBound := ⟨true,false,⟨⟨(157/56212),(1831/84318),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv132 : CertBound := ⟨true,false,⟨⟨(133/21164),(324/5291),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv142 : CertBound := ⟨true,false,⟨⟨(27643479309/3094101131000),(60916023/773525282750),(0),(0)⟩,⟨(897/1606),(1/1606),(0),(0)⟩,⟨(40267/72022),(-1/72022),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv162 : CertBound := ⟨true,false,⟨⟨(2410800350/148777560217),(21990250/148777560217),(0),(0)⟩,⟨(20549/36661),(-1/36661),(0),(0)⟩,⟨(8013/14278),(1/14278),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv304 : CertBound := ⟨true,true,⟨⟨(-93/505),(0),(0),(22/505)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(119/202),(0),(0),(-1/202)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv362 : CertBound := ⟨true,true,⟨⟨(-123/71230),(0),(0),(329/213690)⟩,⟨(465/838),(0),(0),(1/838)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv363 : CertBound := ⟨true,true,⟨⟨(-183/109289),(0),(0),(304/327867)⟩,⟨(323/586),(0),(0),(1/586)⟩,⟨(419/746),(0),(0),(-1/2238)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv433 : CertBound := ⟨true,true,⟨⟨(729/1024),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv447 : CertBound := ⟨false,false,⟨⟨(-3/10),(0),(0),(1/10)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv452 : CertBound := ⟨false,false,⟨⟨(-11/85),(0),(0),(8/255)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv453 : CertBound := ⟨false,false,⟨⟨(-25/202),(0),(0),(7/202)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(119/202),(0),(0),(-1/202)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv487 : CertBound := ⟨false,false,⟨⟨(3194/1638923),(26413/4916769),(0),(0)⟩,⟨(897/1606),(1/1606),(0),(0)⟩,⟨(966/1727),(-1/5181),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv517 : CertBound := ⟨false,false,⟨⟨(4561/892333),(28085/2676999),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(464/827),(-1/2481),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv530 : CertBound := ⟨false,false,⟨⟨(306757/43366226),(152856/21683113),(0),(0)⟩,⟨(29287/52438),(1/52438),(0),(0)⟩,⟨(464/827),(-1/2481),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv567 : CertBound := ⟨false,false,⟨⟨(2210/188243),(16406/564729),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(966/1727),(-1/5181),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv574 : CertBound := ⟨false,false,⟨⟨(868057/66408100),(-3811/66408100),(0),(0)⟩,⟨(897/1606),(1/1606),(0),(0)⟩,⟨(464/827),(-1/2481),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩⟩⟩
noncomputable def bv576 : CertBound := ⟨false,false,⟨⟨(26005350/1963632473),(-8053050/1963632473),(0),(0)⟩,⟨(7079/12661),(1/12661),(0),(0)⟩,⟨(5599/10006),(-1/10006),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv607 : CertBound := ⟨false,false,⟨⟨(39791/1863433),(89003/5590299),(0),(0)⟩,⟨(966/1727),(-1/5181),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv611 : CertBound := ⟨false,false,⟨⟨(32254358000/1470202261803),(1139525000/4410606785409),(0),(0)⟩,⟨(897/1606),(1/1606),(0),(0)⟩,⟨(20549/36661),(-1/36661),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv638 : CertBound := ⟨false,false,⟨⟨(137761350/4981629103),(-42953550/4981629103),(0),(0)⟩,⟨(3591/6406),(1/6406),(0),(0)⟩,⟨(2561/4561),(-1/4561),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv839 : CertBound := ⟨false,false,⟨⟨(9/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv925 : CertBound := ⟨false,true,⟨⟨(106352/63342983),(207341/190028949),(0),(0)⟩,⟨(7079/12661),(1/12661),(0),(0)⟩,⟨(5599/10006),(-1/10006),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv939 : CertBound := ⟨false,true,⟨⟨(50777/14608883),(99116/43826649),(0),(0)⟩,⟨(3591/6406),(1/6406),(0),(0)⟩,⟨(2561/4561),(-1/4561),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv972 : CertBound := ⟨false,true,⟨⟨(27643479309/3094101131000),(60916023/773525282750),(0),(0)⟩,⟨(897/1606),(1/1606),(0),(0)⟩,⟨(40267/72022),(-1/72022),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv999 : CertBound := ⟨false,true,⟨⟨(2410800350/148777560217),(21990250/148777560217),(0),(0)⟩,⟨(20549/36661),(-1/36661),(0),(0)⟩,⟨(8013/14278),(1/14278),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1023 : CertBound := ⟨false,true,⟨⟨(1763569500/71479894733),(-137040500/71479894733),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(20549/36661),(-1/36661),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1052 : CertBound := ⟨false,true,⟨⟨(5983/141700),(279/28340),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1162 : CertBound := ⟨false,true,⟨⟨(225/289),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
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
theorem op147 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = bv1052 := by
  norm_num [bv1052, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op148 : lowerHistoryNormalization ([1,1,3],[]) true true = bv304 := by
  norm_num [bv304, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op149 : lowerHistoryNecessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [bv567] := by
  decide +kernel
theorem op13 : lowerHistoryNormalization ([1,1,3],[1]) false false = bv453 := by
  norm_num [bv453, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op202 : lowerHistoryNecessary ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3],[1]) = some [bv56] := by
  decide +kernel
theorem op45 : lowerHistoryNormalization ([1,1,3,1],[1]) true false = bv31 := by
  norm_num [bv31, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
open BindingNumeric20
theorem op46 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,3,1],[1]) = some [bv607] := by
  decide +kernel
theorem op47 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,3,1],[1]) true = bv162 := by
  norm_num [bv162, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op48 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,3,1],[1]) true = bv611 := by
  norm_num [bv611, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op49 : lowerHistoryPull (lowerHistoryHN) ([1,1,3,1],[1]) true = bv31 := by
  norm_num [bv31, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op50 : lowerHistoryPull (lowerHistoryH2) ([1,1,3,1],[1]) true = bv999 := by
  norm_num [bv999, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op51 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,3,1],[1]) true = bv162 := by
  norm_num [bv162, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op52 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,3,1],[1]) true = bv611 := by
  norm_num [bv611, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op53 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,3,1],[1]) true = bv530 := by
  norm_num [bv530, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op54 : lowerHistoryPull (lowerHistoryH23) ([1,1,3,1],[1]) true = bv1023 := by
  norm_num [bv1023, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op55 : lowerHistoryNormalization ([1,1,3,1,1],[1]) true true = bv362 := by
  norm_num [bv362, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op56 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,3,1,1],[1]) = some [bv517] := by
  decide +kernel
theorem op57 : lowerHistoryPull (lowerHistoryH7) ([1,1,3,1,1],[1]) true = bv638 := by
  norm_num [bv638, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def path1391 : LowerHistoryPath := ⟨.initial,305,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,1,3,1],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1391 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv31,bv607,bv162,bv611,bv31]]
noncomputable def expected1391 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv31,bv607,bv162,bv611]]
theorem structural1391 (ops : RootOps19.SourceOps) (b31 b56 b125 b132 b162 b304 b371 b433 b447 b453 b567 b607 b611 b839 b843 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h13 : ops.normalization ([1,1,3],[1]) false false = b453)
    (h202 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3],[1]) = some [b56])
    (h45 : ops.normalization ([1,1,3,1],[1]) true false = b31)
    (h46 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,3,1],[1]) = some [b607])
    (h47 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,3,1],[1]) true = b162)
    (h48 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,3,1],[1]) true = b611)
    (h49 : ops.pull (lowerHistoryHN) ([1,1,3,1],[1]) true = b31)
    : RootOps19.eval ops path1391 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b453,b56,b31,b607,b162,b611,b31]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1391, h0, h1, h2, h3, h4, h5, h147, h148, h149, h13, h202, h45, h46, h47, h48, h49, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1391 : lowerHistorySourcePremises path1391 = raw1391.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1391 RootOps19.actualOps bv31 bv56 bv125 bv132 bv162 bv304 bv371 bv433 bv447 bv453 bv567 bv607 bv611 bv839 bv843 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op13 op202 op45 op46 op47 op48 op49
theorem dedup1391 : raw1391.map List.eraseDups = expected1391 := by
  decide +kernel
theorem source1391 : lowerHistorySourcePremises path1391 = expected1391 := (rawSource1391).trans (dedup1391)
end M7ContinueSep17.Initial20260918.B1390_1395

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
namespace M7ContinueSep17.Initial20260918.B1390_1395
theorem bound31 : lowerHistoryBound 31 = bv31 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[30]? = some bv31 := Eq.refl (some bv31)
  exact (BoundCompact16.global_to_chunk1 30 (by decide)).trans hl
theorem bound56 : lowerHistoryBound 56 = bv56 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[55]? = some bv56 := Eq.refl (some bv56)
  exact (BoundCompact16.global_to_chunk1 55 (by decide)).trans hl
theorem bound70 : lowerHistoryBound 70 = bv70 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[69]? = some bv70 := Eq.refl (some bv70)
  exact (BoundCompact16.global_to_chunk1 69 (by decide)).trans hl
theorem bound107 : lowerHistoryBound 107 = bv107 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[106]? = some bv107 := Eq.refl (some bv107)
  exact (BoundCompact16.global_to_chunk1 106 (by decide)).trans hl
theorem bound108 : lowerHistoryBound 108 = bv108 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[107]? = some bv108 := Eq.refl (some bv108)
  exact (BoundCompact16.global_to_chunk1 107 (by decide)).trans hl
theorem bound125 : lowerHistoryBound 125 = bv125 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[124]? = some bv125 := Eq.refl (some bv125)
  exact (BoundCompact16.global_to_chunk1 124 (by decide)).trans hl
theorem bound132 : lowerHistoryBound 132 = bv132 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[131]? = some bv132 := Eq.refl (some bv132)
  exact (BoundCompact16.global_to_chunk1 131 (by decide)).trans hl
theorem bound142 : lowerHistoryBound 142 = bv142 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[141]? = some bv142 := Eq.refl (some bv142)
  exact (BoundCompact16.global_to_chunk1 141 (by decide)).trans hl
theorem bound162 : lowerHistoryBound 162 = bv162 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[161]? = some bv162 := Eq.refl (some bv162)
  exact (BoundCompact16.global_to_chunk1 161 (by decide)).trans hl
theorem bound304 : lowerHistoryBound 304 = bv304 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[103]? = some bv304 := Eq.refl (some bv304)
  exact (BoundCompact16.global_to_chunk2 103 (by decide)).trans hl
theorem bound362 : lowerHistoryBound 362 = bv362 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[161]? = some bv362 := Eq.refl (some bv362)
  exact (BoundCompact16.global_to_chunk2 161 (by decide)).trans hl
theorem bound363 : lowerHistoryBound 363 = bv363 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[162]? = some bv363 := Eq.refl (some bv363)
  exact (BoundCompact16.global_to_chunk2 162 (by decide)).trans hl
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
theorem bound452 : lowerHistoryBound 452 = bv452 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[51]? = some bv452 := Eq.refl (some bv452)
  exact (BoundCompact16.global_to_chunk3 51 (by decide)).trans hl
theorem bound453 : lowerHistoryBound 453 = bv453 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[52]? = some bv453 := Eq.refl (some bv453)
  exact (BoundCompact16.global_to_chunk3 52 (by decide)).trans hl
theorem bound487 : lowerHistoryBound 487 = bv487 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[86]? = some bv487 := Eq.refl (some bv487)
  exact (BoundCompact16.global_to_chunk3 86 (by decide)).trans hl
theorem bound517 : lowerHistoryBound 517 = bv517 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[116]? = some bv517 := Eq.refl (some bv517)
  exact (BoundCompact16.global_to_chunk3 116 (by decide)).trans hl
theorem bound530 : lowerHistoryBound 530 = bv530 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[129]? = some bv530 := Eq.refl (some bv530)
  exact (BoundCompact16.global_to_chunk3 129 (by decide)).trans hl
theorem bound567 : lowerHistoryBound 567 = bv567 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[166]? = some bv567 := Eq.refl (some bv567)
  exact (BoundCompact16.global_to_chunk3 166 (by decide)).trans hl
theorem bound574 : lowerHistoryBound 574 = bv574 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[173]? = some bv574 := Eq.refl (some bv574)
  exact (BoundCompact16.global_to_chunk3 173 (by decide)).trans hl
theorem bound576 : lowerHistoryBound 576 = bv576 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[175]? = some bv576 := Eq.refl (some bv576)
  exact (BoundCompact16.global_to_chunk3 175 (by decide)).trans hl
theorem bound607 : lowerHistoryBound 607 = bv607 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[6]? = some bv607 := Eq.refl (some bv607)
  exact (BoundCompact16.global_to_chunk4 6 (by decide)).trans hl
theorem bound611 : lowerHistoryBound 611 = bv611 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[10]? = some bv611 := Eq.refl (some bv611)
  exact (BoundCompact16.global_to_chunk4 10 (by decide)).trans hl
theorem bound638 : lowerHistoryBound 638 = bv638 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[37]? = some bv638 := Eq.refl (some bv638)
  exact (BoundCompact16.global_to_chunk4 37 (by decide)).trans hl
theorem bound839 : lowerHistoryBound 839 = bv839 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[38]? = some bv839 := Eq.refl (some bv839)
  exact (BoundCompact16.global_to_chunk5 38 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound925 : lowerHistoryBound 925 = bv925 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[124]? = some bv925 := Eq.refl (some bv925)
  exact (BoundCompact16.global_to_chunk5 124 (by decide)).trans hl
theorem bound939 : lowerHistoryBound 939 = bv939 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[138]? = some bv939 := Eq.refl (some bv939)
  exact (BoundCompact16.global_to_chunk5 138 (by decide)).trans hl
theorem bound972 : lowerHistoryBound 972 = bv972 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[171]? = some bv972 := Eq.refl (some bv972)
  exact (BoundCompact16.global_to_chunk5 171 (by decide)).trans hl
theorem bound999 : lowerHistoryBound 999 = bv999 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[198]? = some bv999 := Eq.refl (some bv999)
  exact (BoundCompact16.global_to_chunk5 198 (by decide)).trans hl
theorem bound1023 : lowerHistoryBound 1023 = bv1023 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[22]? = some bv1023 := Eq.refl (some bv1023)
  exact (BoundCompact16.global_to_chunk6 22).trans hl
theorem bound1052 : lowerHistoryBound 1052 = bv1052 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[51]? = some bv1052 := Eq.refl (some bv1052)
  exact (BoundCompact16.global_to_chunk6 51).trans hl
theorem bound1162 : lowerHistoryBound 1162 = bv1162 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[161]? = some bv1162 := Eq.refl (some bv1162)
  exact (BoundCompact16.global_to_chunk6 161).trans hl
end M7ContinueSep17.Initial20260918.B1390_1395

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
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def recs1391 : List LowerHistoryRecord := [⟨.initial,305,0,(-1),false,775,380⟩]
theorem records1391 : lowerHistoryRecordsFor (⟨.initial,305,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,1,3,1],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1391 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 305)) = recs1391
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1392 : List LowerHistoryRecord := [⟨.initial,306,0,(-1),false,773,461⟩,⟨.initial,306,1,(-1),false,771,461⟩]
theorem records1392 : lowerHistoryRecordsFor (⟨.initial,306,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,1,3,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1392 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 306)) = recs1392
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1393 : List LowerHistoryRecord := [⟨.initial,307,0,(-1),false,919,370⟩]
theorem records1393 : lowerHistoryRecordsFor (⟨.initial,307,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false)],([3,1,1,3,1],[3,1,3,1]),(false,true),false,4,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1393 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 307)) = recs1393
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1394 : List LowerHistoryRecord := [⟨.initial,308,0,(-1),false,917,446⟩]
theorem records1394 : lowerHistoryRecordsFor (⟨.initial,308,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,1,3,1,2],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1394 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 308)) = recs1394
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1395 : List LowerHistoryRecord := [⟨.initial,309,0,(-1),false,915,461⟩]
theorem records1395 : lowerHistoryRecordsFor (⟨.initial,309,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,1,3,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1395 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 309)) = recs1395
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
end M7ContinueSep17.Initial20260918.B1390_1395

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
namespace M7ContinueSep17.Initial20260918.B1390_1395
theorem premise771 : lowerHistoryPremises[770]? = some ([31,56,107,125,132,162,304,362,371,433,447,453,517,530,567,607,611,638,839,843,939,1023,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[770]? = lowerHistoryPremises04[170]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 170 (by decide)
  exact hg.trans (by rfl)
theorem premise773 : lowerHistoryPremises[772]? = some ([31,56,107,125,132,304,362,371,433,447,453,517,567,607,638,839,843,939,999,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[772]? = lowerHistoryPremises04[172]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 172 (by decide)
  exact hg.trans (by rfl)
theorem premise775 : lowerHistoryPremises[774]? = some ([31,56,125,132,162,304,371,433,447,453,567,607,611,839,843,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[774]? = lowerHistoryPremises04[174]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 174 (by decide)
  exact hg.trans (by rfl)
theorem premise915 : lowerHistoryPremises[914]? = some ([56,70,107,125,132,304,371,433,447,452,453,517,567,638,839,843,939,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[914]? = lowerHistoryPremises05[114]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 114 (by decide)
  exact hg.trans (by rfl)
theorem premise917 : lowerHistoryPremises[916]? = some ([56,70,108,125,132,304,363,371,433,447,452,453,487,567,574,576,839,843,925,972,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[916]? = lowerHistoryPremises05[116]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 116 (by decide)
  exact hg.trans (by rfl)
theorem premise919 : lowerHistoryPremises[918]? = some ([56,70,125,132,142,304,371,433,447,452,453,567,574,839,843,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[918]? = lowerHistoryPremises05[118]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 118 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1390_1395
theorem witness370_projection : (lowerHistoryWitness 370).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 370).upperBound = lowerHistoryBound 574 ∧ (lowerHistoryWitness 370).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[169]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 574, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 574, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[369]? = lowerHistoryWitnesses02[169]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 169 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness380_projection : (lowerHistoryWitness 380).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 380).upperBound = lowerHistoryBound 611 ∧ (lowerHistoryWitness 380).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[179]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 611, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 611, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[379]? = lowerHistoryWitnesses02[179]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 179 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness446_projection : (lowerHistoryWitness 446).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 446).upperBound = lowerHistoryBound 925 ∧ (lowerHistoryWitness 446).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[45]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 925, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 925, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[445]? = lowerHistoryWitnesses03[45]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 45 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness461_projection : (lowerHistoryWitness 461).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 461).upperBound = lowerHistoryBound 939 ∧ (lowerHistoryWitness 461).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[60]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 939, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 939, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[460]? = lowerHistoryWitnesses03[60]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 60 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 370 => (433,574)
  | 380 => (433,611)
  | 446 => (433,925)
  | 461 => (433,939)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 771 => [31,56,107,125,132,162,304,362,371,433,447,453,517,530,567,607,611,638,839,843,939,1023,1052,1162]
  | 773 => [31,56,107,125,132,304,362,371,433,447,453,517,567,607,638,839,843,939,999,1052,1162]
  | 775 => [31,56,125,132,162,304,371,433,447,453,567,607,611,839,843,1052,1162]
  | 915 => [56,70,107,125,132,304,371,433,447,452,453,517,567,638,839,843,939,1052,1162]
  | 917 => [56,70,108,125,132,304,363,371,433,447,452,453,487,567,574,576,839,843,925,972,1052,1162]
  | 919 => [56,70,125,132,142,304,371,433,447,452,453,567,574,839,843,1052,1162]
  | _ => []
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def src1391 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,453,56,31,607,162,611]]
theorem sourceIDs1391 : lowerHistorySourcePremises path1391 = src1391.map (List.map lowerHistoryBound) := by
  have hb : src1391.map (List.map lowerHistoryBound) = expected1391 := by
    simp only [src1391, expected1391, List.map_cons, List.map_nil, bound31, bound56, bound125, bound132, bound162, bound304, bound371, bound433, bound447, bound453, bound567, bound607, bound611, bound839, bound843, bound1052, bound1162]
  exact source1391.trans hb.symm
theorem length1391 : path1391.alternatives = (lowerHistorySourcePremises path1391).length := by
  rw [sourceIDs1391]
  rfl
theorem binding1391 : lowerHistoryPathBinding path1391 := by
  apply BindingIds19.pathBinding_from_ids path1391 src1391 [] recs1391 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1391 rfl records1391 rfl
  · intro r hr _
    simp only [recs1391, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise775)
  · intro r hr _
    simp only [recs1391, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1391] using witness380_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1391 recs1391 records1391 length1391 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
open BindingNumeric20
theorem op58 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,3,1,1],[1]) true = bv939 := by
  norm_num [bv939, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op59 : lowerHistoryPull (lowerHistoryHN) ([1,1,3,1,1],[1]) true = bv107 := by
  norm_num [bv107, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op60 : lowerHistoryNormalization ([1,1,3,1],[1]) false false = bv452 := by
  norm_num [bv452, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op61 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,3,1],[1]) = some [bv70] := by
  decide +kernel
theorem op62 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,3,1],[1]) false = bv574 := by
  norm_num [bv574, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op63 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,3,1],[1]) false = bv142 := by
  norm_num [bv142, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op64 : lowerHistoryPull (lowerHistoryHN) ([1,1,3,1],[1]) false = bv452 := by
  norm_num [bv452, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op65 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,3,1],[1]) false = bv574 := by
  norm_num [bv574, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op66 : lowerHistoryPull (lowerHistoryH5) ([1,1,3,1],[1]) false = bv972 := by
  norm_num [bv972, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op67 : lowerHistoryNormalization ([1,1,3,1,2],[1]) true true = bv363 := by
  norm_num [bv363, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op68 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1,2],[3,1,3,1]),(true,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,3,1,2],[1]) = some [bv487] := by
  decide +kernel
theorem op69 : lowerHistoryPull (lowerHistoryH7) ([1,1,3,1,2],[1]) true = bv576 := by
  norm_num [bv576, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def path1392 : LowerHistoryPath := ⟨.initial,306,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,1,3,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩
noncomputable def raw1392 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv31,bv607,bv999,bv362,bv517,bv638,bv939,bv107],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv31,bv607,bv162,bv611,bv530,bv1023,bv362,bv517,bv638,bv939,bv107]]
noncomputable def expected1392 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv31,bv607,bv999,bv362,bv517,bv638,bv939,bv107],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv31,bv607,bv162,bv611,bv530,bv1023,bv362,bv517,bv638,bv939,bv107]]
theorem structural1392 (ops : RootOps19.SourceOps) (b31 b56 b107 b125 b132 b162 b304 b362 b371 b433 b447 b453 b517 b530 b567 b607 b611 b638 b839 b843 b939 b999 b1023 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h13 : ops.normalization ([1,1,3],[1]) false false = b453)
    (h202 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3],[1]) = some [b56])
    (h45 : ops.normalization ([1,1,3,1],[1]) true false = b31)
    (h46 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,3,1],[1]) = some [b607])
    (h50 : ops.pull (lowerHistoryH2) ([1,1,3,1],[1]) true = b999)
    (h51 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,3,1],[1]) true = b162)
    (h52 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,3,1],[1]) true = b611)
    (h53 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,3,1],[1]) true = b530)
    (h54 : ops.pull (lowerHistoryH23) ([1,1,3,1],[1]) true = b1023)
    (h55 : ops.normalization ([1,1,3,1,1],[1]) true true = b362)
    (h56 : ops.necessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,3,1,1],[1]) = some [b517])
    (h57 : ops.pull (lowerHistoryH7) ([1,1,3,1,1],[1]) true = b638)
    (h58 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,3,1,1],[1]) true = b939)
    (h59 : ops.pull (lowerHistoryHN) ([1,1,3,1,1],[1]) true = b107)
    : RootOps19.eval ops path1392 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b453,b56,b31,b607,b999,b362,b517,b638,b939,b107],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b453,b56,b31,b607,b162,b611,b530,b1023,b362,b517,b638,b939,b107]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1392, h0, h1, h2, h3, h4, h5, h147, h148, h149, h13, h202, h45, h46, h50, h51, h52, h53, h54, h55, h56, h57, h58, h59, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1392 : lowerHistorySourcePremises path1392 = raw1392.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1392 RootOps19.actualOps bv31 bv56 bv107 bv125 bv132 bv162 bv304 bv362 bv371 bv433 bv447 bv453 bv517 bv530 bv567 bv607 bv611 bv638 bv839 bv843 bv939 bv999 bv1023 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op13 op202 op45 op46 op50 op51 op52 op53 op54 op55 op56 op57 op58 op59
theorem dedup1392 : raw1392.map List.eraseDups = expected1392 := by
  decide +kernel
theorem source1392 : lowerHistorySourcePremises path1392 = expected1392 := (rawSource1392).trans (dedup1392)
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def src1392 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,453,56,31,607,999,362,517,638,939,107],[371,843,433,1162,839,132,447,125,1052,304,567,453,56,31,607,162,611,530,1023,362,517,638,939,107]]
theorem sourceIDs1392 : lowerHistorySourcePremises path1392 = src1392.map (List.map lowerHistoryBound) := by
  have hb : src1392.map (List.map lowerHistoryBound) = expected1392 := by
    simp only [src1392, expected1392, List.map_cons, List.map_nil, bound31, bound56, bound107, bound125, bound132, bound162, bound304, bound362, bound371, bound433, bound447, bound453, bound517, bound530, bound567, bound607, bound611, bound638, bound839, bound843, bound939, bound999, bound1023, bound1052, bound1162]
  exact source1392.trans hb.symm
theorem length1392 : path1392.alternatives = (lowerHistorySourcePremises path1392).length := by
  rw [sourceIDs1392]
  rfl
theorem binding1392 : lowerHistoryPathBinding path1392 := by
  apply BindingIds19.pathBinding_from_ids path1392 src1392 [] recs1392 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1392 rfl records1392 rfl
  · intro r hr _
    simp only [recs1392, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise773)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise771)
  · intro r hr _
    simp only [recs1392, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1392] using witness461_projection
    · simpa only [blockWids, path1392] using witness461_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1392 recs1392 records1392 length1392 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def path1393 : LowerHistoryPath := ⟨.initial,307,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false)],([3,1,1,3,1],[3,1,3,1]),(false,true),false,4,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1393 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv452,bv70,bv574,bv142,bv452]]
noncomputable def expected1393 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv452,bv70,bv574,bv142]]
theorem structural1393 (ops : RootOps19.SourceOps) (b56 b70 b125 b132 b142 b304 b371 b433 b447 b452 b453 b567 b574 b839 b843 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h13 : ops.normalization ([1,1,3],[1]) false false = b453)
    (h202 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3],[1]) = some [b56])
    (h60 : ops.normalization ([1,1,3,1],[1]) false false = b452)
    (h61 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,3,1],[1]) = some [b70])
    (h62 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,3,1],[1]) false = b574)
    (h63 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,3,1],[1]) false = b142)
    (h64 : ops.pull (lowerHistoryHN) ([1,1,3,1],[1]) false = b452)
    : RootOps19.eval ops path1393 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b453,b56,b452,b70,b574,b142,b452]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1393, h0, h1, h2, h3, h4, h5, h147, h148, h149, h13, h202, h60, h61, h62, h63, h64, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1393 : lowerHistorySourcePremises path1393 = raw1393.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1393 RootOps19.actualOps bv56 bv70 bv125 bv132 bv142 bv304 bv371 bv433 bv447 bv452 bv453 bv567 bv574 bv839 bv843 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op13 op202 op60 op61 op62 op63 op64
theorem dedup1393 : raw1393.map List.eraseDups = expected1393 := by
  decide +kernel
theorem source1393 : lowerHistorySourcePremises path1393 = expected1393 := (rawSource1393).trans (dedup1393)
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def src1393 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,453,56,452,70,574,142]]
theorem sourceIDs1393 : lowerHistorySourcePremises path1393 = src1393.map (List.map lowerHistoryBound) := by
  have hb : src1393.map (List.map lowerHistoryBound) = expected1393 := by
    simp only [src1393, expected1393, List.map_cons, List.map_nil, bound56, bound70, bound125, bound132, bound142, bound304, bound371, bound433, bound447, bound452, bound453, bound567, bound574, bound839, bound843, bound1052, bound1162]
  exact source1393.trans hb.symm
theorem length1393 : path1393.alternatives = (lowerHistorySourcePremises path1393).length := by
  rw [sourceIDs1393]
  rfl
theorem binding1393 : lowerHistoryPathBinding path1393 := by
  apply BindingIds19.pathBinding_from_ids path1393 src1393 [] recs1393 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1393 rfl records1393 rfl
  · intro r hr _
    simp only [recs1393, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise919)
  · intro r hr _
    simp only [recs1393, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1393] using witness370_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1393 recs1393 records1393 length1393 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
open BindingNumeric20
theorem op70 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,3,1,2],[1]) true = bv925 := by
  norm_num [bv925, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op71 : lowerHistoryPull (lowerHistoryHN) ([1,1,3,1,2],[1]) true = bv108 := by
  norm_num [bv108, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op72 : lowerHistoryNormalization ([1,1,3,1,1],[1]) true false = bv107 := by
  norm_num [bv107, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op73 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,3,1,1],[1]) = some [bv517] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def path1394 : LowerHistoryPath := ⟨.initial,308,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,1,3,1,2],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1394 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv452,bv70,bv574,bv972,bv363,bv487,bv576,bv925,bv108]]
noncomputable def expected1394 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv452,bv70,bv574,bv972,bv363,bv487,bv576,bv925,bv108]]
theorem structural1394 (ops : RootOps19.SourceOps) (b56 b70 b108 b125 b132 b304 b363 b371 b433 b447 b452 b453 b487 b567 b574 b576 b839 b843 b925 b972 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h13 : ops.normalization ([1,1,3],[1]) false false = b453)
    (h202 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3],[1]) = some [b56])
    (h60 : ops.normalization ([1,1,3,1],[1]) false false = b452)
    (h61 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,3,1],[1]) = some [b70])
    (h65 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,3,1],[1]) false = b574)
    (h66 : ops.pull (lowerHistoryH5) ([1,1,3,1],[1]) false = b972)
    (h67 : ops.normalization ([1,1,3,1,2],[1]) true true = b363)
    (h68 : ops.necessary ⟨⟨([3,1,1,3,1,2],[3,1,3,1]),(true,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,3,1,2],[1]) = some [b487])
    (h69 : ops.pull (lowerHistoryH7) ([1,1,3,1,2],[1]) true = b576)
    (h70 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,3,1,2],[1]) true = b925)
    (h71 : ops.pull (lowerHistoryHN) ([1,1,3,1,2],[1]) true = b108)
    : RootOps19.eval ops path1394 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b453,b56,b452,b70,b574,b972,b363,b487,b576,b925,b108]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1394, h0, h1, h2, h3, h4, h5, h147, h148, h149, h13, h202, h60, h61, h65, h66, h67, h68, h69, h70, h71, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1394 : lowerHistorySourcePremises path1394 = raw1394.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1394 RootOps19.actualOps bv56 bv70 bv108 bv125 bv132 bv304 bv363 bv371 bv433 bv447 bv452 bv453 bv487 bv567 bv574 bv576 bv839 bv843 bv925 bv972 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op13 op202 op60 op61 op65 op66 op67 op68 op69 op70 op71
theorem dedup1394 : raw1394.map List.eraseDups = expected1394 := by
  decide +kernel
theorem source1394 : lowerHistorySourcePremises path1394 = expected1394 := (rawSource1394).trans (dedup1394)
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def src1394 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,453,56,452,70,574,972,363,487,576,925,108]]
theorem sourceIDs1394 : lowerHistorySourcePremises path1394 = src1394.map (List.map lowerHistoryBound) := by
  have hb : src1394.map (List.map lowerHistoryBound) = expected1394 := by
    simp only [src1394, expected1394, List.map_cons, List.map_nil, bound56, bound70, bound108, bound125, bound132, bound304, bound363, bound371, bound433, bound447, bound452, bound453, bound487, bound567, bound574, bound576, bound839, bound843, bound925, bound972, bound1052, bound1162]
  exact source1394.trans hb.symm
theorem length1394 : path1394.alternatives = (lowerHistorySourcePremises path1394).length := by
  rw [sourceIDs1394]
  rfl
theorem binding1394 : lowerHistoryPathBinding path1394 := by
  apply BindingIds19.pathBinding_from_ids path1394 src1394 [] recs1394 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1394 rfl records1394 rfl
  · intro r hr _
    simp only [recs1394, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise917)
  · intro r hr _
    simp only [recs1394, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1394] using witness446_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1394 recs1394 records1394 length1394 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def path1395 : LowerHistoryPath := ⟨.initial,309,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,1,3,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1395 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv452,bv70,bv107,bv517,bv638,bv939,bv107]]
noncomputable def expected1395 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv453,bv56,bv452,bv70,bv107,bv517,bv638,bv939]]
theorem structural1395 (ops : RootOps19.SourceOps) (b56 b70 b107 b125 b132 b304 b371 b433 b447 b452 b453 b517 b567 b638 b839 b843 b939 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h13 : ops.normalization ([1,1,3],[1]) false false = b453)
    (h202 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3],[1]) = some [b56])
    (h60 : ops.normalization ([1,1,3,1],[1]) false false = b452)
    (h61 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,3,1],[1]) = some [b70])
    (h72 : ops.normalization ([1,1,3,1,1],[1]) true false = b107)
    (h73 : ops.necessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,3,1,1],[1]) = some [b517])
    (h57 : ops.pull (lowerHistoryH7) ([1,1,3,1,1],[1]) true = b638)
    (h58 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,3,1,1],[1]) true = b939)
    (h59 : ops.pull (lowerHistoryHN) ([1,1,3,1,1],[1]) true = b107)
    : RootOps19.eval ops path1395 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b453,b56,b452,b70,b107,b517,b638,b939,b107]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3,1]),(true,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1395, h0, h1, h2, h3, h4, h5, h147, h148, h149, h13, h202, h60, h61, h72, h73, h57, h58, h59, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1395 : lowerHistorySourcePremises path1395 = raw1395.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1395 RootOps19.actualOps bv56 bv70 bv107 bv125 bv132 bv304 bv371 bv433 bv447 bv452 bv453 bv517 bv567 bv638 bv839 bv843 bv939 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op13 op202 op60 op61 op72 op73 op57 op58 op59
theorem dedup1395 : raw1395.map List.eraseDups = expected1395 := by
  decide +kernel
theorem source1395 : lowerHistorySourcePremises path1395 = expected1395 := (rawSource1395).trans (dedup1395)
end M7ContinueSep17.Initial20260918.B1390_1395

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1390_1395
noncomputable def src1395 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,453,56,452,70,107,517,638,939]]
theorem sourceIDs1395 : lowerHistorySourcePremises path1395 = src1395.map (List.map lowerHistoryBound) := by
  have hb : src1395.map (List.map lowerHistoryBound) = expected1395 := by
    simp only [src1395, expected1395, List.map_cons, List.map_nil, bound56, bound70, bound107, bound125, bound132, bound304, bound371, bound433, bound447, bound452, bound453, bound517, bound567, bound638, bound839, bound843, bound939, bound1052, bound1162]
  exact source1395.trans hb.symm
theorem length1395 : path1395.alternatives = (lowerHistorySourcePremises path1395).length := by
  rw [sourceIDs1395]
  rfl
theorem binding1395 : lowerHistoryPathBinding path1395 := by
  apply BindingIds19.pathBinding_from_ids path1395 src1395 [] recs1395 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1395 rfl records1395 rfl
  · intro r hr _
    simp only [recs1395, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise915)
  · intro r hr _
    simp only [recs1395, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1395] using witness461_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1395 recs1395 records1395 length1395 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1390_1395

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
namespace M7ContinueSep17.Initial20260918.B1390_1395
theorem _root_.solution : lowerHistoryBindingBatch 1390 1395 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1390]? = some M7ContinueSep17.Initial20260918.B1390_1395.path1391 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 304 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1391
  · have hl : lowerHistoryPaths[1391]? = some M7ContinueSep17.Initial20260918.B1390_1395.path1392 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 305 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1392
  · have hl : lowerHistoryPaths[1392]? = some M7ContinueSep17.Initial20260918.B1390_1395.path1393 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 306 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1393
  · have hl : lowerHistoryPaths[1393]? = some M7ContinueSep17.Initial20260918.B1390_1395.path1394 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 307 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1394
  · have hl : lowerHistoryPaths[1394]? = some M7ContinueSep17.Initial20260918.B1390_1395.path1395 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 308 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1395
end M7ContinueSep17.Initial20260918.B1390_1395

#print axioms solution
