-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1375_1380
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T07:00:35.659994+00:00
-- url     : https://prove2.me/submissions/e09f80a9-fe9f-4585-9a86-0266be3e9b1d

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
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def bv70 : CertBound := ⟨true,false,⟨⟨(-415417/30547726),(945823/91643178),(0),(0)⟩,⟨(897/1606),(1/1606),(0),(0)⟩,⟨(464/827),(-1/2481),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv91 : CertBound := ⟨true,false,⟨⟨(-3346571/672008618),(2548863/672008618),(0),(0)⟩,⟨(3591/6406),(1/6406),(0),(0)⟩,⟨(2561/4561),(-1/4561),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv100 : CertBound := ⟨true,false,⟨⟨(-3671/1436585),(0),(0),(2608/4309755)⟩,⟨(18977/33802),(0),(0),(1/33802)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv101 : CertBound := ⟨true,false,⟨⟨(-81/32810),(0),(0),(451/689010)⟩,⟨(1083/1930),(0),(0),(1/13510)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv107 : CertBound := ⟨true,false,⟨⟨(-123/71230),(0),(0),(329/213690)⟩,⟨(465/838),(0),(0),(1/838)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv115 : CertBound := ⟨true,false,⟨⟨(-517/1189618),(0),(0),(355/1189618)⟩,⟨(3159/5638),(0),(0),(1/5638)⟩,⟨(1189/2110),(0),(0),(-1/2110)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv117 : CertBound := ⟨true,false,⟨⟨(657448091650/1005736569061367),(7495208750/1005736569061367),(0),(0)⟩,⟨(528973/941974),(-1/941974),(0),(0)⟩,⟨(191780/341497),(1/341497),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv118 : CertBound := ⟨true,false,⟨⟨(11581182850/10299093711959),(374544650/30897281135877),(0),(0)⟩,⟨(304439/542422),(-1/542422),(0),(0)⟩,⟨(37497/66803),(1/200409),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv120 : CertBound := ⟨true,false,⟨⟨(1399681/1003351310),(900643/2508378275),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(4018/7153),(-1/7153),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv125 : CertBound := ⟨true,false,⟨⟨(157/56212),(1831/84318),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv132 : CertBound := ⟨true,false,⟨⟨(133/21164),(324/5291),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv304 : CertBound := ⟨true,true,⟨⟨(-93/505),(0),(0),(22/505)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(119/202),(0),(0),(-1/202)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv305 : CertBound := ⟨true,true,⟨⟨(-31/170),(0),(0),(7/170)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv356 : CertBound := ⟨true,true,⟨⟨(-3671/1436585),(0),(0),(2608/4309755)⟩,⟨(18977/33802),(0),(0),(1/33802)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv357 : CertBound := ⟨true,true,⟨⟨(-81/32810),(0),(0),(451/689010)⟩,⟨(1083/1930),(0),(0),(1/13510)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv369 : CertBound := ⟨true,true,⟨⟨(-517/1189618),(0),(0),(355/1189618)⟩,⟨(3159/5638),(0),(0),(1/5638)⟩,⟨(1189/2110),(0),(0),(-1/2110)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv433 : CertBound := ⟨true,true,⟨⟨(729/1024),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv447 : CertBound := ⟨false,false,⟨⟨(-3/10),(0),(0),(1/10)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv452 : CertBound := ⟨false,false,⟨⟨(-11/85),(0),(0),(8/255)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv463 : CertBound := ⟨false,false,⟨⟨(-123/71230),(0),(0),(329/213690)⟩,⟨(465/838),(0),(0),(1/838)⟩,⟨(97/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv464 : CertBound := ⟨false,false,⟨⟨(28838419/89068906043),(64517527/267206718129),(0),(0)⟩,⟨(11267/20063),(-1/60189),(0),(0)⟩,⟨(191780/341497),(1/341497),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv466 : CertBound := ⟨false,false,⟨⟨(13483180/31755464533),(30930496/31755464533),(0),(0)⟩,⟨(191780/341497),(1/341497),(0),(0)⟩,⟨(4018/7153),(-1/7153),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv470 : CertBound := ⟨false,false,⟨⟨(28549/38481157),(74110/38481157),(0),(0)⟩,⟨(8013/14278),(1/14278),(0),(0)⟩,⟨(2561/4561),(-1/4561),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv474 : CertBound := ⟨false,false,⟨⟨(912210062000/1171115038817163),(106324325000/3513345116451489),(0),(0)⟩,⟨(27956/49789),(1/49789),(0),(0)⟩,⟨(528973/941974),(-1/941974),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv476 : CertBound := ⟨false,false,⟨⟨(3365743650/2952799402003),(-1058293950/2952799402003),(0),(0)⟩,⟨(91910/163669),(1/163669),(0),(0)⟩,⟨(59425/105814),(-1/105814),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv481 : CertBound := ⟨false,false,⟨⟨(512751182000/370538214709707),(1840159000/41170912745523),(0),(0)⟩,⟨(5117/9119),(1/27357),(0),(0)⟩,⟨(304439/542422),(-1/542422),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv517 : CertBound := ⟨false,false,⟨⟨(4561/892333),(28085/2676999),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(464/827),(-1/2481),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv546 : CertBound := ⟨false,false,⟨⟨(123/13031),(3064/430023),(0),(0)⟩,⟨(966/1727),(-1/5181),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv567 : CertBound := ⟨false,false,⟨⟨(2210/188243),(16406/564729),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(966/1727),(-1/5181),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv638 : CertBound := ⟨false,false,⟨⟨(137761350/4981629103),(-42953550/4981629103),(0),(0)⟩,⟨(3591/6406),(1/6406),(0),(0)⟩,⟨(2561/4561),(-1/4561),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv659 : CertBound := ⟨false,false,⟨⟨(26613/652223),(-13973/652223),(0),(0)⟩,⟨(2561/4561),(-1/4561),(0),(0)⟩,⟨(82/143),(-1/143),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv839 : CertBound := ⟨false,false,⟨⟨(9/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv909 : CertBound := ⟨false,true,⟨⟨(111568/787203253),(218119/2361609759),(0),(0)⟩,⟨(91910/163669),(1/163669),(0),(0)⟩,⟨(59425/105814),(-1/105814),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv915 : CertBound := ⟨false,true,⟨⟨(657448091650/1005736569061367),(7495208750/1005736569061367),(0),(0)⟩,⟨(528973/941974),(-1/941974),(0),(0)⟩,⟨(191780/341497),(1/341497),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv921 : CertBound := ⟨false,true,⟨⟨(1399681/1003351310),(900643/2508378275),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(4018/7153),(-1/7153),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv939 : CertBound := ⟨false,true,⟨⟨(50777/14608883),(99116/43826649),(0),(0)⟩,⟨(3591/6406),(1/6406),(0),(0)⟩,⟨(2561/4561),(-1/4561),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1008 : CertBound := ⟨false,true,⟨⟨(814400/41470451),(-5150/124411353),(0),(0)⟩,⟨(966/1727),(-1/5181),(0),(0)⟩,⟨(8013/14278),(1/14278),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1052 : CertBound := ⟨false,true,⟨⟨(5983/141700),(279/28340),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1162 : CertBound := ⟨false,true,⟨⟨(225/289),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
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
theorem op150 : lowerHistoryPull (lowerHistoryH2) ([1,1,3],[]) true = bv1008 := by
  norm_num [bv1008, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op151 : lowerHistoryNormalization ([1,1,3,1],[]) true true = bv305 := by
  norm_num [bv305, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op152 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,3,1],[]) = some [bv546] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
open BindingNumeric20
theorem op60 : lowerHistoryNormalization ([1,1,3,1],[1]) false false = bv452 := by
  norm_num [bv452, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op153 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3,1],[1]) = some [bv70] := by
  decide +kernel
theorem op72 : lowerHistoryNormalization ([1,1,3,1,1],[1]) true false = bv107 := by
  norm_num [bv107, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op73 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,3,1,1],[1]) = some [bv517] := by
  decide +kernel
theorem op57 : lowerHistoryPull (lowerHistoryH7) ([1,1,3,1,1],[1]) true = bv638 := by
  norm_num [bv638, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op58 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,3,1,1],[1]) true = bv939 := by
  norm_num [bv939, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op59 : lowerHistoryPull (lowerHistoryHN) ([1,1,3,1,1],[1]) true = bv107 := by
  norm_num [bv107, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op154 : lowerHistoryNormalization ([1,1,3,1,1],[1]) false false = bv463 := by
  norm_num [bv463, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op155 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,3,1,1],[1]) = some [bv91] := by
  decide +kernel
theorem op156 : lowerHistoryPull (lowerHistoryH7) ([1,1,3,1,1],[1]) false = bv120 := by
  norm_num [bv120, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op157 : lowerHistoryPull (lowerHistoryHN) ([1,1,3,1,1],[1]) false = bv463 := by
  norm_num [bv463, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op158 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,3,1,1],[1]) false = bv921 := by
  norm_num [bv921, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def path1376 : LowerHistoryPath := ⟨.initial,290,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,1,3,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1376 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv107,bv517,bv638,bv939,bv107]]
noncomputable def expected1376 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv107,bv517,bv638,bv939]]
theorem structural1376 (ops : RootOps19.SourceOps) (b70 b107 b125 b132 b304 b305 b371 b433 b447 b452 b517 b546 b567 b638 b839 b843 b939 b1008 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h150 : ops.pull (lowerHistoryH2) ([1,1,3],[]) true = b1008)
    (h151 : ops.normalization ([1,1,3,1],[]) true true = b305)
    (h152 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,3,1],[]) = some [b546])
    (h60 : ops.normalization ([1,1,3,1],[1]) false false = b452)
    (h153 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3,1],[1]) = some [b70])
    (h72 : ops.normalization ([1,1,3,1,1],[1]) true false = b107)
    (h73 : ops.necessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,3,1,1],[1]) = some [b517])
    (h57 : ops.pull (lowerHistoryH7) ([1,1,3,1,1],[1]) true = b638)
    (h58 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,3,1,1],[1]) true = b939)
    (h59 : ops.pull (lowerHistoryHN) ([1,1,3,1,1],[1]) true = b107)
    : RootOps19.eval ops path1376 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b1008,b305,b546,b452,b70,b107,b517,b638,b939,b107]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1376, h0, h1, h2, h3, h4, h5, h147, h148, h149, h150, h151, h152, h60, h153, h72, h73, h57, h58, h59, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1376 : lowerHistorySourcePremises path1376 = raw1376.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1376 RootOps19.actualOps bv70 bv107 bv125 bv132 bv304 bv305 bv371 bv433 bv447 bv452 bv517 bv546 bv567 bv638 bv839 bv843 bv939 bv1008 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op150 op151 op152 op60 op153 op72 op73 op57 op58 op59
theorem dedup1376 : raw1376.map List.eraseDups = expected1376 := by
  decide +kernel
theorem source1376 : lowerHistorySourcePremises path1376 = expected1376 := (rawSource1376).trans (dedup1376)
end M7ContinueSep17.Initial20260918.B1375_1380

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
namespace M7ContinueSep17.Initial20260918.B1375_1380
theorem bound70 : lowerHistoryBound 70 = bv70 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[69]? = some bv70 := Eq.refl (some bv70)
  exact (BoundCompact16.global_to_chunk1 69 (by decide)).trans hl
theorem bound91 : lowerHistoryBound 91 = bv91 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[90]? = some bv91 := Eq.refl (some bv91)
  exact (BoundCompact16.global_to_chunk1 90 (by decide)).trans hl
theorem bound100 : lowerHistoryBound 100 = bv100 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[99]? = some bv100 := Eq.refl (some bv100)
  exact (BoundCompact16.global_to_chunk1 99 (by decide)).trans hl
theorem bound101 : lowerHistoryBound 101 = bv101 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[100]? = some bv101 := Eq.refl (some bv101)
  exact (BoundCompact16.global_to_chunk1 100 (by decide)).trans hl
theorem bound107 : lowerHistoryBound 107 = bv107 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[106]? = some bv107 := Eq.refl (some bv107)
  exact (BoundCompact16.global_to_chunk1 106 (by decide)).trans hl
theorem bound115 : lowerHistoryBound 115 = bv115 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[114]? = some bv115 := Eq.refl (some bv115)
  exact (BoundCompact16.global_to_chunk1 114 (by decide)).trans hl
theorem bound117 : lowerHistoryBound 117 = bv117 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[116]? = some bv117 := Eq.refl (some bv117)
  exact (BoundCompact16.global_to_chunk1 116 (by decide)).trans hl
theorem bound118 : lowerHistoryBound 118 = bv118 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[117]? = some bv118 := Eq.refl (some bv118)
  exact (BoundCompact16.global_to_chunk1 117 (by decide)).trans hl
theorem bound120 : lowerHistoryBound 120 = bv120 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[119]? = some bv120 := Eq.refl (some bv120)
  exact (BoundCompact16.global_to_chunk1 119 (by decide)).trans hl
theorem bound125 : lowerHistoryBound 125 = bv125 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[124]? = some bv125 := Eq.refl (some bv125)
  exact (BoundCompact16.global_to_chunk1 124 (by decide)).trans hl
theorem bound132 : lowerHistoryBound 132 = bv132 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[131]? = some bv132 := Eq.refl (some bv132)
  exact (BoundCompact16.global_to_chunk1 131 (by decide)).trans hl
theorem bound304 : lowerHistoryBound 304 = bv304 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[103]? = some bv304 := Eq.refl (some bv304)
  exact (BoundCompact16.global_to_chunk2 103 (by decide)).trans hl
theorem bound305 : lowerHistoryBound 305 = bv305 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[104]? = some bv305 := Eq.refl (some bv305)
  exact (BoundCompact16.global_to_chunk2 104 (by decide)).trans hl
theorem bound356 : lowerHistoryBound 356 = bv356 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[155]? = some bv356 := Eq.refl (some bv356)
  exact (BoundCompact16.global_to_chunk2 155 (by decide)).trans hl
theorem bound357 : lowerHistoryBound 357 = bv357 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[156]? = some bv357 := Eq.refl (some bv357)
  exact (BoundCompact16.global_to_chunk2 156 (by decide)).trans hl
theorem bound369 : lowerHistoryBound 369 = bv369 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[168]? = some bv369 := Eq.refl (some bv369)
  exact (BoundCompact16.global_to_chunk2 168 (by decide)).trans hl
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
theorem bound463 : lowerHistoryBound 463 = bv463 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[62]? = some bv463 := Eq.refl (some bv463)
  exact (BoundCompact16.global_to_chunk3 62 (by decide)).trans hl
theorem bound464 : lowerHistoryBound 464 = bv464 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[63]? = some bv464 := Eq.refl (some bv464)
  exact (BoundCompact16.global_to_chunk3 63 (by decide)).trans hl
theorem bound466 : lowerHistoryBound 466 = bv466 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[65]? = some bv466 := Eq.refl (some bv466)
  exact (BoundCompact16.global_to_chunk3 65 (by decide)).trans hl
theorem bound470 : lowerHistoryBound 470 = bv470 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[69]? = some bv470 := Eq.refl (some bv470)
  exact (BoundCompact16.global_to_chunk3 69 (by decide)).trans hl
theorem bound474 : lowerHistoryBound 474 = bv474 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[73]? = some bv474 := Eq.refl (some bv474)
  exact (BoundCompact16.global_to_chunk3 73 (by decide)).trans hl
theorem bound476 : lowerHistoryBound 476 = bv476 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[75]? = some bv476 := Eq.refl (some bv476)
  exact (BoundCompact16.global_to_chunk3 75 (by decide)).trans hl
theorem bound481 : lowerHistoryBound 481 = bv481 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[80]? = some bv481 := Eq.refl (some bv481)
  exact (BoundCompact16.global_to_chunk3 80 (by decide)).trans hl
theorem bound517 : lowerHistoryBound 517 = bv517 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[116]? = some bv517 := Eq.refl (some bv517)
  exact (BoundCompact16.global_to_chunk3 116 (by decide)).trans hl
theorem bound546 : lowerHistoryBound 546 = bv546 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[145]? = some bv546 := Eq.refl (some bv546)
  exact (BoundCompact16.global_to_chunk3 145 (by decide)).trans hl
theorem bound567 : lowerHistoryBound 567 = bv567 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[166]? = some bv567 := Eq.refl (some bv567)
  exact (BoundCompact16.global_to_chunk3 166 (by decide)).trans hl
theorem bound638 : lowerHistoryBound 638 = bv638 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[37]? = some bv638 := Eq.refl (some bv638)
  exact (BoundCompact16.global_to_chunk4 37 (by decide)).trans hl
theorem bound659 : lowerHistoryBound 659 = bv659 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[58]? = some bv659 := Eq.refl (some bv659)
  exact (BoundCompact16.global_to_chunk4 58 (by decide)).trans hl
theorem bound839 : lowerHistoryBound 839 = bv839 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[38]? = some bv839 := Eq.refl (some bv839)
  exact (BoundCompact16.global_to_chunk5 38 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound909 : lowerHistoryBound 909 = bv909 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[108]? = some bv909 := Eq.refl (some bv909)
  exact (BoundCompact16.global_to_chunk5 108 (by decide)).trans hl
theorem bound915 : lowerHistoryBound 915 = bv915 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[114]? = some bv915 := Eq.refl (some bv915)
  exact (BoundCompact16.global_to_chunk5 114 (by decide)).trans hl
theorem bound921 : lowerHistoryBound 921 = bv921 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[120]? = some bv921 := Eq.refl (some bv921)
  exact (BoundCompact16.global_to_chunk5 120 (by decide)).trans hl
theorem bound939 : lowerHistoryBound 939 = bv939 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[138]? = some bv939 := Eq.refl (some bv939)
  exact (BoundCompact16.global_to_chunk5 138 (by decide)).trans hl
theorem bound1008 : lowerHistoryBound 1008 = bv1008 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[7]? = some bv1008 := Eq.refl (some bv1008)
  exact (BoundCompact16.global_to_chunk6 7).trans hl
theorem bound1052 : lowerHistoryBound 1052 = bv1052 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[51]? = some bv1052 := Eq.refl (some bv1052)
  exact (BoundCompact16.global_to_chunk6 51).trans hl
theorem bound1162 : lowerHistoryBound 1162 = bv1162 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[161]? = some bv1162 := Eq.refl (some bv1162)
  exact (BoundCompact16.global_to_chunk6 161).trans hl
end M7ContinueSep17.Initial20260918.B1375_1380

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
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def recs1376 : List LowerHistoryRecord := [⟨.initial,290,0,(-1),false,1013,461⟩]
theorem records1376 : lowerHistoryRecordsFor (⟨.initial,290,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,1,3,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1376 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 290)) = recs1376
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1377 : List LowerHistoryRecord := [⟨.initial,291,0,(-1),false,1012,341⟩]
theorem records1377 : lowerHistoryRecordsFor (⟨.initial,291,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,1,1,3,1,1],[3,1,3,1]),(true,true),false,2,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1377 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 291)) = recs1377
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1378 : List LowerHistoryRecord := [⟨.initial,292,0,(-1),false,1002,343⟩]
theorem records1378 : lowerHistoryRecordsFor (⟨.initial,292,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,1,3,1,1,3],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1378 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 292)) = recs1378
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1379 : List LowerHistoryRecord := [⟨.initial,293,0,(-1),false,1001,424⟩]
theorem records1379 : lowerHistoryRecordsFor (⟨.initial,293,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,1,3,1,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1379 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 293)) = recs1379
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1380 : List LowerHistoryRecord := [⟨.initial,294,0,(-1),false,1011,347⟩,⟨.initial,294,1,(-1),false,1010,347⟩]
theorem records1380 : lowerHistoryRecordsFor (⟨.initial,294,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,1,3,1,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1380 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 294)) = recs1380
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
end M7ContinueSep17.Initial20260918.B1375_1380

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
namespace M7ContinueSep17.Initial20260918.B1375_1380
theorem premise1001 : lowerHistoryPremises[1000]? = some ([70,91,100,125,132,304,305,356,357,371,433,447,452,463,464,466,476,546,567,839,843,909,915,921,1008,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1000]? = lowerHistoryPremises06[0]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 0 (by decide)
  exact hg.trans (by rfl)
theorem premise1002 : lowerHistoryPremises[1001]? = some ([70,91,101,117,125,132,304,305,357,371,433,447,452,463,466,474,546,567,839,843,921,1008,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1001]? = lowerHistoryPremises06[1]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 1 (by decide)
  exact hg.trans (by rfl)
theorem premise1010 : lowerHistoryPremises[1009]? = some ([70,91,115,118,120,125,132,304,305,369,371,433,447,452,463,470,481,546,567,659,839,843,1008,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1009]? = lowerHistoryPremises06[9]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 9 (by decide)
  exact hg.trans (by rfl)
theorem premise1011 : lowerHistoryPremises[1010]? = some ([70,91,115,118,125,132,304,305,369,371,433,447,452,463,470,481,546,567,839,843,921,1008,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1010]? = lowerHistoryPremises06[10]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 10 (by decide)
  exact hg.trans (by rfl)
theorem premise1012 : lowerHistoryPremises[1011]? = some ([70,91,120,125,132,304,305,371,433,447,452,463,546,567,839,843,1008,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1011]? = lowerHistoryPremises06[11]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 11 (by decide)
  exact hg.trans (by rfl)
theorem premise1013 : lowerHistoryPremises[1012]? = some ([70,107,125,132,304,305,371,433,447,452,517,546,567,638,839,843,939,1008,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[1012]? = lowerHistoryPremises06[12]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 12 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1375_1380
theorem witness341_projection : (lowerHistoryWitness 341).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 341).upperBound = lowerHistoryBound 463 ∧ (lowerHistoryWitness 341).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[140]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 463, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 463, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[340]? = lowerHistoryWitnesses02[140]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 140 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness343_projection : (lowerHistoryWitness 343).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 343).upperBound = lowerHistoryBound 474 ∧ (lowerHistoryWitness 343).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[142]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 474, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 474, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[342]? = lowerHistoryWitnesses02[142]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 142 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness347_projection : (lowerHistoryWitness 347).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 347).upperBound = lowerHistoryBound 481 ∧ (lowerHistoryWitness 347).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[146]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 481, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 481, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[346]? = lowerHistoryWitnesses02[146]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 146 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness424_projection : (lowerHistoryWitness 424).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 424).upperBound = lowerHistoryBound 909 ∧ (lowerHistoryWitness 424).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[23]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 909, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 909, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[423]? = lowerHistoryWitnesses03[23]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 23 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness461_projection : (lowerHistoryWitness 461).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 461).upperBound = lowerHistoryBound 939 ∧ (lowerHistoryWitness 461).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[60]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 939, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 939, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[460]? = lowerHistoryWitnesses03[60]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 60 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 341 => (433,463)
  | 343 => (433,474)
  | 347 => (433,481)
  | 424 => (433,909)
  | 461 => (433,939)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 1001 => [70,91,100,125,132,304,305,356,357,371,433,447,452,463,464,466,476,546,567,839,843,909,915,921,1008,1052,1162]
  | 1002 => [70,91,101,117,125,132,304,305,357,371,433,447,452,463,466,474,546,567,839,843,921,1008,1052,1162]
  | 1010 => [70,91,115,118,120,125,132,304,305,369,371,433,447,452,463,470,481,546,567,659,839,843,1008,1052,1162]
  | 1011 => [70,91,115,118,125,132,304,305,369,371,433,447,452,463,470,481,546,567,839,843,921,1008,1052,1162]
  | 1012 => [70,91,120,125,132,304,305,371,433,447,452,463,546,567,839,843,1008,1052,1162]
  | 1013 => [70,107,125,132,304,305,371,433,447,452,517,546,567,638,839,843,939,1008,1052,1162]
  | _ => []
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def src1376 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,1008,305,546,452,70,107,517,638,939]]
theorem sourceIDs1376 : lowerHistorySourcePremises path1376 = src1376.map (List.map lowerHistoryBound) := by
  have hb : src1376.map (List.map lowerHistoryBound) = expected1376 := by
    simp only [src1376, expected1376, List.map_cons, List.map_nil, bound70, bound107, bound125, bound132, bound304, bound305, bound371, bound433, bound447, bound452, bound517, bound546, bound567, bound638, bound839, bound843, bound939, bound1008, bound1052, bound1162]
  exact source1376.trans hb.symm
theorem length1376 : path1376.alternatives = (lowerHistorySourcePremises path1376).length := by
  rw [sourceIDs1376]
  rfl
theorem binding1376 : lowerHistoryPathBinding path1376 := by
  apply BindingIds19.pathBinding_from_ids path1376 src1376 [] recs1376 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1376 rfl records1376 rfl
  · intro r hr _
    simp only [recs1376, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1013)
  · intro r hr _
    simp only [recs1376, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1376] using witness461_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1376 recs1376 records1376 length1376 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def path1377 : LowerHistoryPath := ⟨.initial,291,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,1,1,3,1,1],[3,1,3,1]),(true,true),false,2,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1377 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv120,bv463]]
noncomputable def expected1377 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv120]]
theorem structural1377 (ops : RootOps19.SourceOps) (b70 b91 b120 b125 b132 b304 b305 b371 b433 b447 b452 b463 b546 b567 b839 b843 b1008 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h150 : ops.pull (lowerHistoryH2) ([1,1,3],[]) true = b1008)
    (h151 : ops.normalization ([1,1,3,1],[]) true true = b305)
    (h152 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,3,1],[]) = some [b546])
    (h60 : ops.normalization ([1,1,3,1],[1]) false false = b452)
    (h153 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3,1],[1]) = some [b70])
    (h154 : ops.normalization ([1,1,3,1,1],[1]) false false = b463)
    (h155 : ops.necessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,3,1,1],[1]) = some [b91])
    (h156 : ops.pull (lowerHistoryH7) ([1,1,3,1,1],[1]) false = b120)
    (h157 : ops.pull (lowerHistoryHN) ([1,1,3,1,1],[1]) false = b463)
    : RootOps19.eval ops path1377 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b1008,b305,b546,b452,b70,b463,b91,b120,b463]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1377, h0, h1, h2, h3, h4, h5, h147, h148, h149, h150, h151, h152, h60, h153, h154, h155, h156, h157, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1377 : lowerHistorySourcePremises path1377 = raw1377.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1377 RootOps19.actualOps bv70 bv91 bv120 bv125 bv132 bv304 bv305 bv371 bv433 bv447 bv452 bv463 bv546 bv567 bv839 bv843 bv1008 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op150 op151 op152 op60 op153 op154 op155 op156 op157
theorem dedup1377 : raw1377.map List.eraseDups = expected1377 := by
  decide +kernel
theorem source1377 : lowerHistorySourcePremises path1377 = expected1377 := (rawSource1377).trans (dedup1377)
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def src1377 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,1008,305,546,452,70,463,91,120]]
theorem sourceIDs1377 : lowerHistorySourcePremises path1377 = src1377.map (List.map lowerHistoryBound) := by
  have hb : src1377.map (List.map lowerHistoryBound) = expected1377 := by
    simp only [src1377, expected1377, List.map_cons, List.map_nil, bound70, bound91, bound120, bound125, bound132, bound304, bound305, bound371, bound433, bound447, bound452, bound463, bound546, bound567, bound839, bound843, bound1008, bound1052, bound1162]
  exact source1377.trans hb.symm
theorem length1377 : path1377.alternatives = (lowerHistorySourcePremises path1377).length := by
  rw [sourceIDs1377]
  rfl
theorem binding1377 : lowerHistoryPathBinding path1377 := by
  apply BindingIds19.pathBinding_from_ids path1377 src1377 [] recs1377 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1377 rfl records1377 rfl
  · intro r hr _
    simp only [recs1377, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1012)
  · intro r hr _
    simp only [recs1377, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1377] using witness341_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1377 recs1377 records1377 length1377 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
open BindingNumeric20
theorem op159 : lowerHistoryNormalization ([1,1,3,1,1,3],[1]) true true = bv357 := by
  norm_num [bv357, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op160 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,3,1,1,3],[1]) = some [bv466] := by
  decide +kernel
theorem op161 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,3,1,1,3],[1]) true = bv117 := by
  norm_num [bv117, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op162 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,3,1,1,3],[1]) true = bv474 := by
  norm_num [bv474, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op163 : lowerHistoryPull (lowerHistoryHN) ([1,1,3,1,1,3],[1]) true = bv101 := by
  norm_num [bv101, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op164 : lowerHistoryPull (lowerHistoryH2) ([1,1,3,1,1,3],[1]) true = bv915 := by
  norm_num [bv915, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op165 : lowerHistoryNormalization ([1,1,3,1,1,3,1],[1]) true true = bv356 := by
  norm_num [bv356, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op166 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,3,1,1,3,1],[1]) = some [bv464] := by
  decide +kernel
theorem op167 : lowerHistoryPull (lowerHistoryH7) ([1,1,3,1,1,3,1],[1]) true = bv476 := by
  norm_num [bv476, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op168 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,3,1,1,3,1],[1]) true = bv909 := by
  norm_num [bv909, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op169 : lowerHistoryPull (lowerHistoryHN) ([1,1,3,1,1,3,1],[1]) true = bv100 := by
  norm_num [bv100, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op170 : lowerHistoryPull (lowerHistoryH9) ([1,1,3,1,1],[1]) false = bv659 := by
  norm_num [bv659, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def path1378 : LowerHistoryPath := ⟨.initial,292,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,1,3,1,1,3],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1378 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv921,bv357,bv466,bv117,bv474,bv101]]
noncomputable def expected1378 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv921,bv357,bv466,bv117,bv474,bv101]]
theorem structural1378 (ops : RootOps19.SourceOps) (b70 b91 b101 b117 b125 b132 b304 b305 b357 b371 b433 b447 b452 b463 b466 b474 b546 b567 b839 b843 b921 b1008 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h150 : ops.pull (lowerHistoryH2) ([1,1,3],[]) true = b1008)
    (h151 : ops.normalization ([1,1,3,1],[]) true true = b305)
    (h152 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,3,1],[]) = some [b546])
    (h60 : ops.normalization ([1,1,3,1],[1]) false false = b452)
    (h153 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3,1],[1]) = some [b70])
    (h154 : ops.normalization ([1,1,3,1,1],[1]) false false = b463)
    (h155 : ops.necessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,3,1,1],[1]) = some [b91])
    (h158 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,3,1,1],[1]) false = b921)
    (h159 : ops.normalization ([1,1,3,1,1,3],[1]) true true = b357)
    (h160 : ops.necessary ⟨⟨([3,1,1,3,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,3,1,1,3],[1]) = some [b466])
    (h161 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,3,1,1,3],[1]) true = b117)
    (h162 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,3,1,1,3],[1]) true = b474)
    (h163 : ops.pull (lowerHistoryHN) ([1,1,3,1,1,3],[1]) true = b101)
    : RootOps19.eval ops path1378 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b1008,b305,b546,b452,b70,b463,b91,b921,b357,b466,b117,b474,b101]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1378, h0, h1, h2, h3, h4, h5, h147, h148, h149, h150, h151, h152, h60, h153, h154, h155, h158, h159, h160, h161, h162, h163, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1378 : lowerHistorySourcePremises path1378 = raw1378.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1378 RootOps19.actualOps bv70 bv91 bv101 bv117 bv125 bv132 bv304 bv305 bv357 bv371 bv433 bv447 bv452 bv463 bv466 bv474 bv546 bv567 bv839 bv843 bv921 bv1008 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op150 op151 op152 op60 op153 op154 op155 op158 op159 op160 op161 op162 op163
theorem dedup1378 : raw1378.map List.eraseDups = expected1378 := by
  decide +kernel
theorem source1378 : lowerHistorySourcePremises path1378 = expected1378 := (rawSource1378).trans (dedup1378)
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def src1378 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,1008,305,546,452,70,463,91,921,357,466,117,474,101]]
theorem sourceIDs1378 : lowerHistorySourcePremises path1378 = src1378.map (List.map lowerHistoryBound) := by
  have hb : src1378.map (List.map lowerHistoryBound) = expected1378 := by
    simp only [src1378, expected1378, List.map_cons, List.map_nil, bound70, bound91, bound101, bound117, bound125, bound132, bound304, bound305, bound357, bound371, bound433, bound447, bound452, bound463, bound466, bound474, bound546, bound567, bound839, bound843, bound921, bound1008, bound1052, bound1162]
  exact source1378.trans hb.symm
theorem length1378 : path1378.alternatives = (lowerHistorySourcePremises path1378).length := by
  rw [sourceIDs1378]
  rfl
theorem binding1378 : lowerHistoryPathBinding path1378 := by
  apply BindingIds19.pathBinding_from_ids path1378 src1378 [] recs1378 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1378 rfl records1378 rfl
  · intro r hr _
    simp only [recs1378, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1002)
  · intro r hr _
    simp only [recs1378, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1378] using witness343_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1378 recs1378 records1378 length1378 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def path1379 : LowerHistoryPath := ⟨.initial,293,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,1,3,1,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1379 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv921,bv357,bv466,bv915,bv356,bv464,bv476,bv909,bv100]]
noncomputable def expected1379 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv921,bv357,bv466,bv915,bv356,bv464,bv476,bv909,bv100]]
theorem structural1379 (ops : RootOps19.SourceOps) (b70 b91 b100 b125 b132 b304 b305 b356 b357 b371 b433 b447 b452 b463 b464 b466 b476 b546 b567 b839 b843 b909 b915 b921 b1008 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h150 : ops.pull (lowerHistoryH2) ([1,1,3],[]) true = b1008)
    (h151 : ops.normalization ([1,1,3,1],[]) true true = b305)
    (h152 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,3,1],[]) = some [b546])
    (h60 : ops.normalization ([1,1,3,1],[1]) false false = b452)
    (h153 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3,1],[1]) = some [b70])
    (h154 : ops.normalization ([1,1,3,1,1],[1]) false false = b463)
    (h155 : ops.necessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,3,1,1],[1]) = some [b91])
    (h158 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,3,1,1],[1]) false = b921)
    (h159 : ops.normalization ([1,1,3,1,1,3],[1]) true true = b357)
    (h160 : ops.necessary ⟨⟨([3,1,1,3,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,3,1,1,3],[1]) = some [b466])
    (h164 : ops.pull (lowerHistoryH2) ([1,1,3,1,1,3],[1]) true = b915)
    (h165 : ops.normalization ([1,1,3,1,1,3,1],[1]) true true = b356)
    (h166 : ops.necessary ⟨⟨([3,1,1,3,1,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,3,1,1,3,1],[1]) = some [b464])
    (h167 : ops.pull (lowerHistoryH7) ([1,1,3,1,1,3,1],[1]) true = b476)
    (h168 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,3,1,1,3,1],[1]) true = b909)
    (h169 : ops.pull (lowerHistoryHN) ([1,1,3,1,1,3,1],[1]) true = b100)
    : RootOps19.eval ops path1379 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b1008,b305,b546,b452,b70,b463,b91,b921,b357,b466,b915,b356,b464,b476,b909,b100]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc6 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf6 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1379, h0, h1, h2, h3, h4, h5, h147, h148, h149, h150, h151, h152, h60, h153, h154, h155, h158, h159, h160, h164, h165, h166, h167, h168, h169, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hf0, hf1, hf2, hf3, hf4, hf5, hf6, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1379 : lowerHistorySourcePremises path1379 = raw1379.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1379 RootOps19.actualOps bv70 bv91 bv100 bv125 bv132 bv304 bv305 bv356 bv357 bv371 bv433 bv447 bv452 bv463 bv464 bv466 bv476 bv546 bv567 bv839 bv843 bv909 bv915 bv921 bv1008 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op150 op151 op152 op60 op153 op154 op155 op158 op159 op160 op164 op165 op166 op167 op168 op169
theorem dedup1379 : raw1379.map List.eraseDups = expected1379 := by
  decide +kernel
theorem source1379 : lowerHistorySourcePremises path1379 = expected1379 := (rawSource1379).trans (dedup1379)
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def src1379 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,1008,305,546,452,70,463,91,921,357,466,915,356,464,476,909,100]]
theorem sourceIDs1379 : lowerHistorySourcePremises path1379 = src1379.map (List.map lowerHistoryBound) := by
  have hb : src1379.map (List.map lowerHistoryBound) = expected1379 := by
    simp only [src1379, expected1379, List.map_cons, List.map_nil, bound70, bound91, bound100, bound125, bound132, bound304, bound305, bound356, bound357, bound371, bound433, bound447, bound452, bound463, bound464, bound466, bound476, bound546, bound567, bound839, bound843, bound909, bound915, bound921, bound1008, bound1052, bound1162]
  exact source1379.trans hb.symm
theorem length1379 : path1379.alternatives = (lowerHistorySourcePremises path1379).length := by
  rw [sourceIDs1379]
  rfl
theorem binding1379 : lowerHistoryPathBinding path1379 := by
  apply BindingIds19.pathBinding_from_ids path1379 src1379 [] recs1379 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1379 rfl records1379 rfl
  · intro r hr _
    simp only [recs1379, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1001)
  · intro r hr _
    simp only [recs1379, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1379] using witness424_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1379 recs1379 records1379 length1379 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
open BindingNumeric20
theorem op171 : lowerHistoryNormalization ([1,1,3,1,1,2],[1]) true true = bv369 := by
  norm_num [bv369, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op172 : lowerHistoryNecessary ⟨⟨([3,1,1,3,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,3,1,1,2],[1]) = some [bv470] := by
  decide +kernel
theorem op173 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,3,1,1,2],[1]) true = bv118 := by
  norm_num [bv118, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op174 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,3,1,1,2],[1]) true = bv481 := by
  norm_num [bv481, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op175 : lowerHistoryPull (lowerHistoryHN) ([1,1,3,1,1,2],[1]) true = bv115 := by
  norm_num [bv115, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def path1380 : LowerHistoryPath := ⟨.initial,294,[3],([1],[]),false,[(([1],[]),false),(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,1,3,1,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩
noncomputable def raw1380 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv921,bv369,bv470,bv118,bv481,bv115],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv120,bv659,bv369,bv470,bv118,bv481,bv115]]
noncomputable def expected1380 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv921,bv369,bv470,bv118,bv481,bv115],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv304,bv567,bv1008,bv305,bv546,bv452,bv70,bv463,bv91,bv120,bv659,bv369,bv470,bv118,bv481,bv115]]
theorem structural1380 (ops : RootOps19.SourceOps) (b70 b91 b115 b118 b120 b125 b132 b304 b305 b369 b371 b433 b447 b452 b463 b470 b481 b546 b567 b659 b839 b843 b921 b1008 b1052 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h147 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h148 : ops.normalization ([1,1,3],[]) true true = b304)
    (h149 : ops.necessary ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([1,1,3],[]) = some [b567])
    (h150 : ops.pull (lowerHistoryH2) ([1,1,3],[]) true = b1008)
    (h151 : ops.normalization ([1,1,3,1],[]) true true = b305)
    (h152 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,3,1],[]) = some [b546])
    (h60 : ops.normalization ([1,1,3,1],[1]) false false = b452)
    (h153 : ops.necessary ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,3,1],[1]) = some [b70])
    (h154 : ops.normalization ([1,1,3,1,1],[1]) false false = b463)
    (h155 : ops.necessary ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,3,1,1],[1]) = some [b91])
    (h158 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,3,1,1],[1]) false = b921)
    (h156 : ops.pull (lowerHistoryH7) ([1,1,3,1,1],[1]) false = b120)
    (h170 : ops.pull (lowerHistoryH9) ([1,1,3,1,1],[1]) false = b659)
    (h171 : ops.normalization ([1,1,3,1,1,2],[1]) true true = b369)
    (h172 : ops.necessary ⟨⟨([3,1,1,3,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,3,1,1,2],[1]) = some [b470])
    (h173 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,3,1,1,2],[1]) true = b118)
    (h174 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,3,1,1,2],[1]) true = b481)
    (h175 : ops.pull (lowerHistoryHN) ([1,1,3,1,1,2],[1]) true = b115)
    : RootOps19.eval ops path1380 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b1008,b305,b546,b452,b70,b463,b91,b921,b369,b470,b118,b481,b115],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b304,b567,b1008,b305,b546,b452,b70,b463,b91,b120,b659,b369,b470,b118,b481,b115]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,3],[3,1,3]),(true,false)⟩,true,false,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([3,1,1,3,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1380, h0, h1, h2, h3, h4, h5, h147, h148, h149, h150, h151, h152, h60, h153, h154, h155, h158, h156, h170, h171, h172, h173, h174, h175, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1380 : lowerHistorySourcePremises path1380 = raw1380.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1380 RootOps19.actualOps bv70 bv91 bv115 bv118 bv120 bv125 bv132 bv304 bv305 bv369 bv371 bv433 bv447 bv452 bv463 bv470 bv481 bv546 bv567 bv659 bv839 bv843 bv921 bv1008 bv1052 bv1162 op0 op1 op2 op3 op4 op5 op147 op148 op149 op150 op151 op152 op60 op153 op154 op155 op158 op156 op170 op171 op172 op173 op174 op175
theorem dedup1380 : raw1380.map List.eraseDups = expected1380 := by
  decide +kernel
theorem source1380 : lowerHistorySourcePremises path1380 = expected1380 := (rawSource1380).trans (dedup1380)
end M7ContinueSep17.Initial20260918.B1375_1380

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1375_1380
noncomputable def src1380 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,304,567,1008,305,546,452,70,463,91,921,369,470,118,481,115],[371,843,433,1162,839,132,447,125,1052,304,567,1008,305,546,452,70,463,91,120,659,369,470,118,481,115]]
theorem sourceIDs1380 : lowerHistorySourcePremises path1380 = src1380.map (List.map lowerHistoryBound) := by
  have hb : src1380.map (List.map lowerHistoryBound) = expected1380 := by
    simp only [src1380, expected1380, List.map_cons, List.map_nil, bound70, bound91, bound115, bound118, bound120, bound125, bound132, bound304, bound305, bound369, bound371, bound433, bound447, bound452, bound463, bound470, bound481, bound546, bound567, bound659, bound839, bound843, bound921, bound1008, bound1052, bound1162]
  exact source1380.trans hb.symm
theorem length1380 : path1380.alternatives = (lowerHistorySourcePremises path1380).length := by
  rw [sourceIDs1380]
  rfl
theorem binding1380 : lowerHistoryPathBinding path1380 := by
  apply BindingIds19.pathBinding_from_ids path1380 src1380 [] recs1380 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1380 rfl records1380 rfl
  · intro r hr _
    simp only [recs1380, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1011)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1010)
  · intro r hr _
    simp only [recs1380, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1380] using witness347_projection
    · simpa only [blockWids, path1380] using witness347_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1380 recs1380 records1380 length1380 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1375_1380

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
namespace M7ContinueSep17.Initial20260918.B1375_1380
theorem _root_.solution : lowerHistoryBindingBatch 1375 1380 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1375]? = some M7ContinueSep17.Initial20260918.B1375_1380.path1376 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 289 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1376
  · have hl : lowerHistoryPaths[1376]? = some M7ContinueSep17.Initial20260918.B1375_1380.path1377 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 290 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1377
  · have hl : lowerHistoryPaths[1377]? = some M7ContinueSep17.Initial20260918.B1375_1380.path1378 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 291 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1378
  · have hl : lowerHistoryPaths[1378]? = some M7ContinueSep17.Initial20260918.B1375_1380.path1379 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 292 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1379
  · have hl : lowerHistoryPaths[1379]? = some M7ContinueSep17.Initial20260918.B1375_1380.path1380 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 293 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1380
end M7ContinueSep17.Initial20260918.B1375_1380

#print axioms solution
