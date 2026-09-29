-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1255_1260
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T06:18:58.735187+00:00
-- url     : https://prove2.me/submissions/46876db0-8e49-4045-a670-4efa6b6d3711

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
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def bv10 : CertBound := ⟨true,false,⟨⟨(-721/2162),(1649/6486),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv29 : CertBound := ⟨true,false,⟨⟨(-42503/322621),(96952/967863),(0),(0)⟩,⟨(51/83),(1/249),(0),(0)⟩,⟨(108/169),(-1/169),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv33 : CertBound := ⟨true,false,⟨⟨(-11/85),(0),(0),(8/255)⟩,⟨(107/170),(0),(0),(1/510)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv35 : CertBound := ⟨true,false,⟨⟨(-25/202),(0),(0),(7/202)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(119/202),(0),(0),(-1/202)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv39 : CertBound := ⟨true,false,⟨⟨(-1/10),(0),(0),(11/210)⟩,⟨(1/2),(0),(0),(1/42)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv59 : CertBound := ⟨true,false,⟨⟨(-37/1394),(0),(0),(27/1394)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(53/82),(0),(0),(-1/82)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv167 : CertBound := ⟨true,false,⟨⟨(24271462850/1370729503247),(277885250/1370729503247),(0),(0)⟩,⟨(22291/34801),(-1/34801),(0),(0)⟩,⟨(8079/12598),(1/12598),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv198 : CertBound := ⟨true,false,⟨⟨(16337/442780),(22537/2213900),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(169/262),(-1/262),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv273 : CertBound := ⟨true,false,⟨⟨(3300/6623),(-50/19869),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv288 : CertBound := ⟨true,false,⟨⟨(9/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv300 : CertBound := ⟨true,true,⟨⟨(-3/10),(0),(0),(1/10)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv310 : CertBound := ⟨true,true,⟨⟨(-11/85),(0),(0),(8/255)⟩,⟨(107/170),(0),(0),(1/510)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv311 : CertBound := ⟨true,true,⟨⟨(-25/202),(0),(0),(7/202)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(119/202),(0),(0),(-1/202)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv324 : CertBound := ⟨true,true,⟨⟨(-37/1394),(0),(0),(27/1394)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(53/82),(0),(0),(-1/82)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv433 : CertBound := ⟨true,true,⟨⟨(729/1024),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv455 : CertBound := ⟨false,false,⟨⟨(-1/10),(0),(0),(11/210)⟩,⟨(1/2),(0),(0),(1/42)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv457 : CertBound := ⟨false,false,⟨⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv562 : CertBound := ⟨false,false,⟨⟨(120860/10727197),(283806/10727197),(0),(0)⟩,⟨(8079/12598),(1/12598),(0),(0)⟩,⟨(169/262),(-1/262),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv605 : CertBound := ⟨false,false,⟨⟨(865727000/41132589537),(306550000/370193305833),(0),(0)⟩,⟨(1179/1846),(1/1846),(0),(0)⟩,⟨(22291/34801),(-1/34801),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv641 : CertBound := ⟨false,false,⟨⟨(69380/2447159),(470752/7341477),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(966/1727),(-1/5181),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv678 : CertBound := ⟨false,false,⟨⟨(1606/31993),(12287/95979),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv745 : CertBound := ⟨false,false,⟨⟨(5/37),(12/37),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv750 : CertBound := ⟨false,false,⟨⟨(88/611),(165/611),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv770 : CertBound := ⟨false,false,⟨⟨(14036700/78144583),(-4337600/78144583),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(142/251),(-1/753),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv794 : CertBound := ⟨false,false,⟨⟨(23655300/73779101),(-7334400/73779101),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(241/409),(-1/409),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv796 : CertBound := ⟨false,false,⟨⟨(2556589/7891300),(703/7891300),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩⟩⟩
noncomputable def bv800 : CertBound := ⟨false,false,⟨⟨(18137/53132),(6217/26566),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(555/718),(-1/718),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv812 : CertBound := ⟨false,false,⟨⟨(1/2),(5/6),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv835 : CertBound := ⟨false,false,⟨⟨(3491100/4783207),(-1092800/4783207),(0),(0)⟩,⟨(51/83),(1/249),(0),(0)⟩,⟨(108/169),(-1/169),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv838 : CertBound := ⟨false,false,⟨⟨(160000/183117),(-80500/1648053),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(66/179),(-1/537),(0),(0)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv1017 : CertBound := ⟨false,true,⟨⟨(1427/62499),(309/20833),(0),(0)⟩,⟨(511/913),(1/913),(0),(0)⟩,⟨(142/251),(-1/753),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1043 : CertBound := ⟨false,true,⟨⟨(16337/442780),(22537/2213900),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(169/262),(-1/262),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1049 : CertBound := ⟨false,true,⟨⟨(8781/216361),(17123/649083),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(241/409),(-1/409),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1090 : CertBound := ⟨false,true,⟨⟨(3841/42081),(2501/42081),(0),(0)⟩,⟨(51/83),(1/249),(0),(0)⟩,⟨(108/169),(-1/169),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1095 : CertBound := ⟨false,true,⟨⟨(5818379/59868250),(142163/5986825),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1101 : CertBound := ⟨false,true,⟨⟨(94425327/860964400),(0),(0),(9188109/860964400)⟩,⟨(1189/2110),(0),(0),(1/2110)⟩,⟨(119/202),(0),(0),(-1/202)⟩,⟨(107/170),(0),(0),(1/510)⟩,⟨(11/10),(0),(0),(-1/10)⟩⟩⟩
noncomputable def bv1123 : CertBound := ⟨false,true,⟨⟨(16996959/80597750),(798219/161195500),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(1741/3013),(-1/3013),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1151 : CertBound := ⟨false,true,⟨⟨(3300/6623),(-50/19869),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1162 : CertBound := ⟨false,true,⟨⟨(225/289),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv1163 : CertBound := ⟨false,true,⟨⟨(254000/323453),(-27500/323453),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [bv371,bv843,bv433,bv1162] := by
  decide +kernel
theorem op1 : ([] : List CertBound) = [] := by
  decide +kernel
theorem op36 : lowerHistoryNormalization ([1],[]) true false = bv288 := by
  norm_num [bv288, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op37 : lowerHistoryNecessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([1],[]) = some [bv812] := by
  decide +kernel
theorem op38 : lowerHistoryPull (lowerHistoryH2) ([1],[]) true = bv1151 := by
  norm_num [bv1151, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op39 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) true = bv273 := by
  norm_num [bv273, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op40 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) true = bv838 := by
  norm_num [bv838, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op41 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1],[]) true = bv800 := by
  norm_num [bv800, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op42 : lowerHistoryPull (lowerHistoryH23) ([1],[]) true = bv1163 := by
  norm_num [bv1163, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op43 : lowerHistoryNormalization ([1,1],[]) true true = bv300 := by
  norm_num [bv300, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op44 : lowerHistoryNecessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1],[]) = some [bv745] := by
  decide +kernel
theorem op45 : lowerHistoryNormalization ([1,1],[1]) false false = bv457 := by
  norm_num [bv457, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
open BindingNumeric20
theorem op46 : lowerHistoryNecessary ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1],[1]) = some [bv10] := by
  decide +kernel
theorem op50 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1],[1]) false = bv796 := by
  norm_num [bv796, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op51 : lowerHistoryPull (lowerHistoryH5) ([1,1],[1]) false = bv1123 := by
  norm_num [bv1123, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op52 : lowerHistoryPull (lowerHistoryH6) ([1,1],[1]) false = bv1101 := by
  norm_num [bv1101, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op53 : lowerHistoryPull (lowerHistoryH7Mixed) ([1,1],[1]) false = bv1095 := by
  norm_num [bv1095, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op54 : lowerHistoryNormalization ([1,1,3],[1]) true true = bv311 := by
  norm_num [bv311, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op55 : lowerHistoryNecessary ⟨⟨([2,1,1,3],[3,1,3,1]),(true,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,3],[1]) = some [bv641] := by
  decide +kernel
theorem op56 : lowerHistoryPull (lowerHistoryH7) ([1,1,3],[1]) true = bv770 := by
  norm_num [bv770, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op57 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,3],[1]) true = bv1017 := by
  norm_num [bv1017, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op58 : lowerHistoryPull (lowerHistoryHN) ([1,1,3],[1]) true = bv35 := by
  norm_num [bv35, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op59 : lowerHistoryNormalization ([1,1,2],[1]) true true = bv324 := by
  norm_num [bv324, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op60 : lowerHistoryNecessary ⟨⟨([2,1,1,2],[3,1,3,1]),(true,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,2],[1]) = some [bv678] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def path1256 : LowerHistoryPath := ⟨.initial,170,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([3],[]),true)],([2,1,1,3],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩
noncomputable def raw1256 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv796,bv1123,bv1101,bv1095,bv311,bv641,bv770,bv1017,bv35],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv796,bv1123,bv1101,bv1095,bv311,bv641,bv770,bv1017,bv35]]
noncomputable def expected1256 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv796,bv1123,bv1101,bv1095,bv311,bv641,bv770,bv1017,bv35],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv796,bv1123,bv1101,bv1095,bv311,bv641,bv770,bv1017,bv35]]
theorem structural1256 (ops : RootOps19.SourceOps) (b10 b35 b273 b288 b300 b311 b371 b433 b457 b641 b745 b770 b796 b800 b812 b838 b843 b1017 b1095 b1101 b1123 b1151 b1162 b1163 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h36 : ops.normalization ([1],[]) true false = b288)
    (h37 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([1],[]) = some [b812])
    (h38 : ops.pull (lowerHistoryH2) ([1],[]) true = b1151)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) true = b273)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) true = b838)
    (h41 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1],[]) true = b800)
    (h42 : ops.pull (lowerHistoryH23) ([1],[]) true = b1163)
    (h43 : ops.normalization ([1,1],[]) true true = b300)
    (h44 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1],[]) = some [b745])
    (h45 : ops.normalization ([1,1],[1]) false false = b457)
    (h46 : ops.necessary ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1],[1]) = some [b10])
    (h50 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1],[1]) false = b796)
    (h51 : ops.pull (lowerHistoryH5) ([1,1],[1]) false = b1123)
    (h52 : ops.pull (lowerHistoryH6) ([1,1],[1]) false = b1101)
    (h53 : ops.pull (lowerHistoryH7Mixed) ([1,1],[1]) false = b1095)
    (h54 : ops.normalization ([1,1,3],[1]) true true = b311)
    (h55 : ops.necessary ⟨⟨([2,1,1,3],[3,1,3,1]),(true,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,3],[1]) = some [b641])
    (h56 : ops.pull (lowerHistoryH7) ([1,1,3],[1]) true = b770)
    (h57 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,3],[1]) true = b1017)
    (h58 : ops.pull (lowerHistoryHN) ([1,1,3],[1]) true = b35)
    : RootOps19.eval ops path1256 = ([[b371,b843,b433,b1162,b288,b812,b1151,b300,b745,b457,b10,b796,b1123,b1101,b1095,b311,b641,b770,b1017,b35],[b371,b843,b433,b1162,b288,b812,b273,b838,b800,b1163,b300,b745,b457,b10,b796,b1123,b1101,b1095,b311,b641,b770,b1017,b35]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,lowerHistoryH7Mixed]] := by rfl
  have hf0 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1256, h0, h1, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h50, h51, h52, h53, h54, h55, h56, h57, h58, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1256 : lowerHistorySourcePremises path1256 = raw1256.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1256 RootOps19.actualOps bv10 bv35 bv273 bv288 bv300 bv311 bv371 bv433 bv457 bv641 bv745 bv770 bv796 bv800 bv812 bv838 bv843 bv1017 bv1095 bv1101 bv1123 bv1151 bv1162 bv1163 op0 op1 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op46 op50 op51 op52 op53 op54 op55 op56 op57 op58
theorem dedup1256 : raw1256.map List.eraseDups = expected1256 := by
  decide +kernel
theorem source1256 : lowerHistorySourcePremises path1256 = expected1256 := (rawSource1256).trans (dedup1256)
end M7ContinueSep17.Initial20260918.B1255_1260

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
namespace M7ContinueSep17.Initial20260918.B1255_1260
theorem bound10 : lowerHistoryBound 10 = bv10 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[9]? = some bv10 := Eq.refl (some bv10)
  exact (BoundCompact16.global_to_chunk1 9 (by decide)).trans hl
theorem bound29 : lowerHistoryBound 29 = bv29 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[28]? = some bv29 := Eq.refl (some bv29)
  exact (BoundCompact16.global_to_chunk1 28 (by decide)).trans hl
theorem bound33 : lowerHistoryBound 33 = bv33 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[32]? = some bv33 := Eq.refl (some bv33)
  exact (BoundCompact16.global_to_chunk1 32 (by decide)).trans hl
theorem bound35 : lowerHistoryBound 35 = bv35 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[34]? = some bv35 := Eq.refl (some bv35)
  exact (BoundCompact16.global_to_chunk1 34 (by decide)).trans hl
theorem bound39 : lowerHistoryBound 39 = bv39 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[38]? = some bv39 := Eq.refl (some bv39)
  exact (BoundCompact16.global_to_chunk1 38 (by decide)).trans hl
theorem bound59 : lowerHistoryBound 59 = bv59 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[58]? = some bv59 := Eq.refl (some bv59)
  exact (BoundCompact16.global_to_chunk1 58 (by decide)).trans hl
theorem bound167 : lowerHistoryBound 167 = bv167 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[166]? = some bv167 := Eq.refl (some bv167)
  exact (BoundCompact16.global_to_chunk1 166 (by decide)).trans hl
theorem bound198 : lowerHistoryBound 198 = bv198 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[197]? = some bv198 := Eq.refl (some bv198)
  exact (BoundCompact16.global_to_chunk1 197 (by decide)).trans hl
theorem bound273 : lowerHistoryBound 273 = bv273 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[72]? = some bv273 := Eq.refl (some bv273)
  exact (BoundCompact16.global_to_chunk2 72 (by decide)).trans hl
theorem bound288 : lowerHistoryBound 288 = bv288 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[87]? = some bv288 := Eq.refl (some bv288)
  exact (BoundCompact16.global_to_chunk2 87 (by decide)).trans hl
theorem bound300 : lowerHistoryBound 300 = bv300 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[99]? = some bv300 := Eq.refl (some bv300)
  exact (BoundCompact16.global_to_chunk2 99 (by decide)).trans hl
theorem bound310 : lowerHistoryBound 310 = bv310 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[109]? = some bv310 := Eq.refl (some bv310)
  exact (BoundCompact16.global_to_chunk2 109 (by decide)).trans hl
theorem bound311 : lowerHistoryBound 311 = bv311 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[110]? = some bv311 := Eq.refl (some bv311)
  exact (BoundCompact16.global_to_chunk2 110 (by decide)).trans hl
theorem bound324 : lowerHistoryBound 324 = bv324 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[123]? = some bv324 := Eq.refl (some bv324)
  exact (BoundCompact16.global_to_chunk2 123 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound433 : lowerHistoryBound 433 = bv433 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[32]? = some bv433 := Eq.refl (some bv433)
  exact (BoundCompact16.global_to_chunk3 32 (by decide)).trans hl
theorem bound455 : lowerHistoryBound 455 = bv455 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[54]? = some bv455 := Eq.refl (some bv455)
  exact (BoundCompact16.global_to_chunk3 54 (by decide)).trans hl
theorem bound457 : lowerHistoryBound 457 = bv457 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[56]? = some bv457 := Eq.refl (some bv457)
  exact (BoundCompact16.global_to_chunk3 56 (by decide)).trans hl
theorem bound562 : lowerHistoryBound 562 = bv562 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[161]? = some bv562 := Eq.refl (some bv562)
  exact (BoundCompact16.global_to_chunk3 161 (by decide)).trans hl
theorem bound605 : lowerHistoryBound 605 = bv605 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[4]? = some bv605 := Eq.refl (some bv605)
  exact (BoundCompact16.global_to_chunk4 4 (by decide)).trans hl
theorem bound641 : lowerHistoryBound 641 = bv641 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[40]? = some bv641 := Eq.refl (some bv641)
  exact (BoundCompact16.global_to_chunk4 40 (by decide)).trans hl
theorem bound678 : lowerHistoryBound 678 = bv678 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[77]? = some bv678 := Eq.refl (some bv678)
  exact (BoundCompact16.global_to_chunk4 77 (by decide)).trans hl
theorem bound745 : lowerHistoryBound 745 = bv745 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[144]? = some bv745 := Eq.refl (some bv745)
  exact (BoundCompact16.global_to_chunk4 144 (by decide)).trans hl
theorem bound750 : lowerHistoryBound 750 = bv750 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[149]? = some bv750 := Eq.refl (some bv750)
  exact (BoundCompact16.global_to_chunk4 149 (by decide)).trans hl
theorem bound770 : lowerHistoryBound 770 = bv770 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[169]? = some bv770 := Eq.refl (some bv770)
  exact (BoundCompact16.global_to_chunk4 169 (by decide)).trans hl
theorem bound794 : lowerHistoryBound 794 = bv794 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[193]? = some bv794 := Eq.refl (some bv794)
  exact (BoundCompact16.global_to_chunk4 193 (by decide)).trans hl
theorem bound796 : lowerHistoryBound 796 = bv796 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[195]? = some bv796 := Eq.refl (some bv796)
  exact (BoundCompact16.global_to_chunk4 195 (by decide)).trans hl
theorem bound800 : lowerHistoryBound 800 = bv800 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[199]? = some bv800 := Eq.refl (some bv800)
  exact (BoundCompact16.global_to_chunk4 199 (by decide)).trans hl
theorem bound812 : lowerHistoryBound 812 = bv812 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[11]? = some bv812 := Eq.refl (some bv812)
  exact (BoundCompact16.global_to_chunk5 11 (by decide)).trans hl
theorem bound835 : lowerHistoryBound 835 = bv835 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[34]? = some bv835 := Eq.refl (some bv835)
  exact (BoundCompact16.global_to_chunk5 34 (by decide)).trans hl
theorem bound838 : lowerHistoryBound 838 = bv838 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[37]? = some bv838 := Eq.refl (some bv838)
  exact (BoundCompact16.global_to_chunk5 37 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound1017 : lowerHistoryBound 1017 = bv1017 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[16]? = some bv1017 := Eq.refl (some bv1017)
  exact (BoundCompact16.global_to_chunk6 16).trans hl
theorem bound1043 : lowerHistoryBound 1043 = bv1043 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[42]? = some bv1043 := Eq.refl (some bv1043)
  exact (BoundCompact16.global_to_chunk6 42).trans hl
theorem bound1049 : lowerHistoryBound 1049 = bv1049 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[48]? = some bv1049 := Eq.refl (some bv1049)
  exact (BoundCompact16.global_to_chunk6 48).trans hl
theorem bound1090 : lowerHistoryBound 1090 = bv1090 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[89]? = some bv1090 := Eq.refl (some bv1090)
  exact (BoundCompact16.global_to_chunk6 89).trans hl
theorem bound1095 : lowerHistoryBound 1095 = bv1095 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[94]? = some bv1095 := Eq.refl (some bv1095)
  exact (BoundCompact16.global_to_chunk6 94).trans hl
theorem bound1101 : lowerHistoryBound 1101 = bv1101 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[100]? = some bv1101 := Eq.refl (some bv1101)
  exact (BoundCompact16.global_to_chunk6 100).trans hl
theorem bound1123 : lowerHistoryBound 1123 = bv1123 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[122]? = some bv1123 := Eq.refl (some bv1123)
  exact (BoundCompact16.global_to_chunk6 122).trans hl
theorem bound1151 : lowerHistoryBound 1151 = bv1151 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[150]? = some bv1151 := Eq.refl (some bv1151)
  exact (BoundCompact16.global_to_chunk6 150).trans hl
theorem bound1162 : lowerHistoryBound 1162 = bv1162 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[161]? = some bv1162 := Eq.refl (some bv1162)
  exact (BoundCompact16.global_to_chunk6 161).trans hl
theorem bound1163 : lowerHistoryBound 1163 = bv1163 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[162]? = some bv1163 := Eq.refl (some bv1163)
  exact (BoundCompact16.global_to_chunk6 162).trans hl
end M7ContinueSep17.Initial20260918.B1255_1260

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
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def recs1256 : List LowerHistoryRecord := [⟨.initial,170,0,(-1),false,644,503⟩,⟨.initial,170,1,(-1),false,642,503⟩]
theorem records1256 : lowerHistoryRecordsFor (⟨.initial,170,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([3],[]),true)],([2,1,1,3],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1256 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 170)) = recs1256
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1257 : List LowerHistoryRecord := [⟨.initial,171,0,(-1),false,652,510⟩,⟨.initial,171,1,(-1),false,650,510⟩]
theorem records1257 : lowerHistoryRecordsFor (⟨.initial,171,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([2],[]),true)],([2,1,1,2],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1257 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 171)) = recs1257
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1258 : List LowerHistoryRecord := [⟨.initial,172,0,(-1),false,648,518⟩,⟨.initial,172,1,(-1),false,646,518⟩]
theorem records1258 : lowerHistoryRecordsFor (⟨.initial,172,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([1],[]),true)],([2,1,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1258 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 172)) = recs1258
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1259 : List LowerHistoryRecord := [⟨.initial,173,0,(-1),false,640,332⟩,⟨.initial,173,1,(-1),false,638,332⟩]
theorem records1259 : lowerHistoryRecordsFor (⟨.initial,173,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([1],[]),false)],([2,1,1,1],[3,1,3,1]),(true,true),false,2,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1259 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 173)) = recs1259
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1260 : List LowerHistoryRecord := [⟨.initial,174,0,(-1),false,600,379⟩,⟨.initial,174,1,(-1),false,598,379⟩]
theorem records1260 : lowerHistoryRecordsFor (⟨.initial,174,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([2,1,1,1,3],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1260 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 174)) = recs1260
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
end M7ContinueSep17.Initial20260918.B1255_1260

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
namespace M7ContinueSep17.Initial20260918.B1255_1260
theorem premise598 : lowerHistoryPremises[597]? = some ([10,29,33,167,273,288,300,310,371,433,455,457,562,605,745,800,812,838,843,1043,1162,1163] : List Nat) := by
  have hg : lowerHistoryPremises[597]? = lowerHistoryPremises03[197]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 197 (by decide)
  exact hg.trans (by rfl)
theorem premise600 : lowerHistoryPremises[599]? = some ([10,29,33,167,288,300,310,371,433,455,457,562,605,745,812,843,1043,1151,1162] : List Nat) := by
  have hg : lowerHistoryPremises[599]? = lowerHistoryPremises03[199]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 199 (by decide)
  exact hg.trans (by rfl)
theorem premise638 : lowerHistoryPremises[637]? = some ([10,29,198,273,288,300,371,433,455,457,745,800,812,838,843,1162,1163] : List Nat) := by
  have hg : lowerHistoryPremises[637]? = lowerHistoryPremises04[37]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 37 (by decide)
  exact hg.trans (by rfl)
theorem premise640 : lowerHistoryPremises[639]? = some ([10,29,198,288,300,371,433,455,457,745,812,843,1151,1162] : List Nat) := by
  have hg : lowerHistoryPremises[639]? = lowerHistoryPremises04[39]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 39 (by decide)
  exact hg.trans (by rfl)
theorem premise642 : lowerHistoryPremises[641]? = some ([10,35,273,288,300,311,371,433,457,641,745,770,796,800,812,838,843,1017,1095,1101,1123,1162,1163] : List Nat) := by
  have hg : lowerHistoryPremises[641]? = lowerHistoryPremises04[41]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 41 (by decide)
  exact hg.trans (by rfl)
theorem premise644 : lowerHistoryPremises[643]? = some ([10,35,288,300,311,371,433,457,641,745,770,796,812,843,1017,1095,1101,1123,1151,1162] : List Nat) := by
  have hg : lowerHistoryPremises[643]? = lowerHistoryPremises04[43]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 43 (by decide)
  exact hg.trans (by rfl)
theorem premise646 : lowerHistoryPremises[645]? = some ([10,39,273,288,300,371,433,457,745,750,800,812,835,838,843,1090,1162,1163] : List Nat) := by
  have hg : lowerHistoryPremises[645]? = lowerHistoryPremises04[45]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 45 (by decide)
  exact hg.trans (by rfl)
theorem premise648 : lowerHistoryPremises[647]? = some ([10,39,288,300,371,433,457,745,750,812,835,843,1090,1151,1162] : List Nat) := by
  have hg : lowerHistoryPremises[647]? = lowerHistoryPremises04[47]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 47 (by decide)
  exact hg.trans (by rfl)
theorem premise650 : lowerHistoryPremises[649]? = some ([10,59,273,288,300,324,371,433,457,678,745,794,796,800,812,838,843,1049,1123,1162,1163] : List Nat) := by
  have hg : lowerHistoryPremises[649]? = lowerHistoryPremises04[49]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 49 (by decide)
  exact hg.trans (by rfl)
theorem premise652 : lowerHistoryPremises[651]? = some ([10,59,288,300,324,371,433,457,678,745,794,796,812,843,1049,1123,1151,1162] : List Nat) := by
  have hg : lowerHistoryPremises[651]? = lowerHistoryPremises04[51]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 51 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1255_1260
theorem witness332_projection : (lowerHistoryWitness 332).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 332).upperBound = lowerHistoryBound 455 ∧ (lowerHistoryWitness 332).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[131]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 455, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 455, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[331]? = lowerHistoryWitnesses02[131]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 131 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness379_projection : (lowerHistoryWitness 379).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 379).upperBound = lowerHistoryBound 605 ∧ (lowerHistoryWitness 379).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[178]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 605, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 605, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[378]? = lowerHistoryWitnesses02[178]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 178 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness503_projection : (lowerHistoryWitness 503).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 503).upperBound = lowerHistoryBound 1017 ∧ (lowerHistoryWitness 503).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[102]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 1017, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 1017, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[502]? = lowerHistoryWitnesses03[102]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 102 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness510_projection : (lowerHistoryWitness 510).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 510).upperBound = lowerHistoryBound 1049 ∧ (lowerHistoryWitness 510).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[109]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 1049, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 1049, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[509]? = lowerHistoryWitnesses03[109]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 109 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness518_projection : (lowerHistoryWitness 518).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 518).upperBound = lowerHistoryBound 1090 ∧ (lowerHistoryWitness 518).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[117]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 1090, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 1090, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[517]? = lowerHistoryWitnesses03[117]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 117 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 332 => (433,455)
  | 379 => (433,605)
  | 503 => (433,1017)
  | 510 => (433,1049)
  | 518 => (433,1090)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 598 => [10,29,33,167,273,288,300,310,371,433,455,457,562,605,745,800,812,838,843,1043,1162,1163]
  | 600 => [10,29,33,167,288,300,310,371,433,455,457,562,605,745,812,843,1043,1151,1162]
  | 638 => [10,29,198,273,288,300,371,433,455,457,745,800,812,838,843,1162,1163]
  | 640 => [10,29,198,288,300,371,433,455,457,745,812,843,1151,1162]
  | 642 => [10,35,273,288,300,311,371,433,457,641,745,770,796,800,812,838,843,1017,1095,1101,1123,1162,1163]
  | 644 => [10,35,288,300,311,371,433,457,641,745,770,796,812,843,1017,1095,1101,1123,1151,1162]
  | 646 => [10,39,273,288,300,371,433,457,745,750,800,812,835,838,843,1090,1162,1163]
  | 648 => [10,39,288,300,371,433,457,745,750,812,835,843,1090,1151,1162]
  | 650 => [10,59,273,288,300,324,371,433,457,678,745,794,796,800,812,838,843,1049,1123,1162,1163]
  | 652 => [10,59,288,300,324,371,433,457,678,745,794,796,812,843,1049,1123,1151,1162]
  | _ => []
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def src1256 : List (List Nat) := [[371,843,433,1162,288,812,1151,300,745,457,10,796,1123,1101,1095,311,641,770,1017,35],[371,843,433,1162,288,812,273,838,800,1163,300,745,457,10,796,1123,1101,1095,311,641,770,1017,35]]
theorem sourceIDs1256 : lowerHistorySourcePremises path1256 = src1256.map (List.map lowerHistoryBound) := by
  have hb : src1256.map (List.map lowerHistoryBound) = expected1256 := by
    simp only [src1256, expected1256, List.map_cons, List.map_nil, bound10, bound35, bound273, bound288, bound300, bound311, bound371, bound433, bound457, bound641, bound745, bound770, bound796, bound800, bound812, bound838, bound843, bound1017, bound1095, bound1101, bound1123, bound1151, bound1162, bound1163]
  exact source1256.trans hb.symm
theorem length1256 : path1256.alternatives = (lowerHistorySourcePremises path1256).length := by
  rw [sourceIDs1256]
  rfl
theorem binding1256 : lowerHistoryPathBinding path1256 := by
  apply BindingIds19.pathBinding_from_ids path1256 src1256 [] recs1256 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1256 rfl records1256 rfl
  · intro r hr _
    simp only [recs1256, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise644)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise642)
  · intro r hr _
    simp only [recs1256, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1256] using witness503_projection
    · simpa only [blockWids, path1256] using witness503_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1256 recs1256 records1256 length1256 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
open BindingNumeric20
theorem op61 : lowerHistoryPull (lowerHistoryH7) ([1,1,2],[1]) true = bv794 := by
  norm_num [bv794, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op62 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,2],[1]) true = bv1049 := by
  norm_num [bv1049, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op63 : lowerHistoryPull (lowerHistoryHN) ([1,1,2],[1]) true = bv59 := by
  norm_num [bv59, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op31 : lowerHistoryNormalization ([1,1,1],[1]) true false = bv39 := by
  norm_num [bv39, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op64 : lowerHistoryNecessary ⟨⟨([2,1,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,1],[1]) = some [bv750] := by
  decide +kernel
theorem op33 : lowerHistoryPull (lowerHistoryH7) ([1,1,1],[1]) true = bv835 := by
  norm_num [bv835, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op34 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,1],[1]) true = bv1090 := by
  norm_num [bv1090, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op35 : lowerHistoryPull (lowerHistoryHN) ([1,1,1],[1]) true = bv39 := by
  norm_num [bv39, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op8 : lowerHistoryNormalization ([1,1,1],[1]) false false = bv455 := by
  norm_num [bv455, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op65 : lowerHistoryNecessary ⟨⟨([2,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,1],[1]) = some [bv29] := by
  decide +kernel
theorem op66 : lowerHistoryPull (lowerHistoryH7) ([1,1,1],[1]) false = bv198 := by
  norm_num [bv198, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op67 : lowerHistoryPull (lowerHistoryHN) ([1,1,1],[1]) false = bv455 := by
  norm_num [bv455, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def path1257 : LowerHistoryPath := ⟨.initial,171,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([2],[]),true)],([2,1,1,2],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩
noncomputable def raw1257 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv796,bv1123,bv324,bv678,bv794,bv1049,bv59],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv796,bv1123,bv324,bv678,bv794,bv1049,bv59]]
noncomputable def expected1257 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv796,bv1123,bv324,bv678,bv794,bv1049,bv59],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv796,bv1123,bv324,bv678,bv794,bv1049,bv59]]
theorem structural1257 (ops : RootOps19.SourceOps) (b10 b59 b273 b288 b300 b324 b371 b433 b457 b678 b745 b794 b796 b800 b812 b838 b843 b1049 b1123 b1151 b1162 b1163 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h36 : ops.normalization ([1],[]) true false = b288)
    (h37 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([1],[]) = some [b812])
    (h38 : ops.pull (lowerHistoryH2) ([1],[]) true = b1151)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) true = b273)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) true = b838)
    (h41 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1],[]) true = b800)
    (h42 : ops.pull (lowerHistoryH23) ([1],[]) true = b1163)
    (h43 : ops.normalization ([1,1],[]) true true = b300)
    (h44 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1],[]) = some [b745])
    (h45 : ops.normalization ([1,1],[1]) false false = b457)
    (h46 : ops.necessary ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1],[1]) = some [b10])
    (h50 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1],[1]) false = b796)
    (h51 : ops.pull (lowerHistoryH5) ([1,1],[1]) false = b1123)
    (h59 : ops.normalization ([1,1,2],[1]) true true = b324)
    (h60 : ops.necessary ⟨⟨([2,1,1,2],[3,1,3,1]),(true,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,2],[1]) = some [b678])
    (h61 : ops.pull (lowerHistoryH7) ([1,1,2],[1]) true = b794)
    (h62 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,2],[1]) true = b1049)
    (h63 : ops.pull (lowerHistoryHN) ([1,1,2],[1]) true = b59)
    : RootOps19.eval ops path1257 = ([[b371,b843,b433,b1162,b288,b812,b1151,b300,b745,b457,b10,b796,b1123,b324,b678,b794,b1049,b59],[b371,b843,b433,b1162,b288,b812,b273,b838,b800,b1163,b300,b745,b457,b10,b796,b1123,b324,b678,b794,b1049,b59]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5]] := by rfl
  have hf0 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1257, h0, h1, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h50, h51, h59, h60, h61, h62, h63, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1257 : lowerHistorySourcePremises path1257 = raw1257.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1257 RootOps19.actualOps bv10 bv59 bv273 bv288 bv300 bv324 bv371 bv433 bv457 bv678 bv745 bv794 bv796 bv800 bv812 bv838 bv843 bv1049 bv1123 bv1151 bv1162 bv1163 op0 op1 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op46 op50 op51 op59 op60 op61 op62 op63
theorem dedup1257 : raw1257.map List.eraseDups = expected1257 := by
  decide +kernel
theorem source1257 : lowerHistorySourcePremises path1257 = expected1257 := (rawSource1257).trans (dedup1257)
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def src1257 : List (List Nat) := [[371,843,433,1162,288,812,1151,300,745,457,10,796,1123,324,678,794,1049,59],[371,843,433,1162,288,812,273,838,800,1163,300,745,457,10,796,1123,324,678,794,1049,59]]
theorem sourceIDs1257 : lowerHistorySourcePremises path1257 = src1257.map (List.map lowerHistoryBound) := by
  have hb : src1257.map (List.map lowerHistoryBound) = expected1257 := by
    simp only [src1257, expected1257, List.map_cons, List.map_nil, bound10, bound59, bound273, bound288, bound300, bound324, bound371, bound433, bound457, bound678, bound745, bound794, bound796, bound800, bound812, bound838, bound843, bound1049, bound1123, bound1151, bound1162, bound1163]
  exact source1257.trans hb.symm
theorem length1257 : path1257.alternatives = (lowerHistorySourcePremises path1257).length := by
  rw [sourceIDs1257]
  rfl
theorem binding1257 : lowerHistoryPathBinding path1257 := by
  apply BindingIds19.pathBinding_from_ids path1257 src1257 [] recs1257 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1257 rfl records1257 rfl
  · intro r hr _
    simp only [recs1257, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise652)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise650)
  · intro r hr _
    simp only [recs1257, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1257] using witness510_projection
    · simpa only [blockWids, path1257] using witness510_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1257 recs1257 records1257 length1257 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def path1258 : LowerHistoryPath := ⟨.initial,172,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([1],[]),true)],([2,1,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩
noncomputable def raw1258 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv39,bv750,bv835,bv1090,bv39],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv39,bv750,bv835,bv1090,bv39]]
noncomputable def expected1258 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv39,bv750,bv835,bv1090],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv39,bv750,bv835,bv1090]]
theorem structural1258 (ops : RootOps19.SourceOps) (b10 b39 b273 b288 b300 b371 b433 b457 b745 b750 b800 b812 b835 b838 b843 b1090 b1151 b1162 b1163 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h36 : ops.normalization ([1],[]) true false = b288)
    (h37 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([1],[]) = some [b812])
    (h38 : ops.pull (lowerHistoryH2) ([1],[]) true = b1151)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) true = b273)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) true = b838)
    (h41 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1],[]) true = b800)
    (h42 : ops.pull (lowerHistoryH23) ([1],[]) true = b1163)
    (h43 : ops.normalization ([1,1],[]) true true = b300)
    (h44 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1],[]) = some [b745])
    (h45 : ops.normalization ([1,1],[1]) false false = b457)
    (h46 : ops.necessary ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1],[1]) = some [b10])
    (h31 : ops.normalization ([1,1,1],[1]) true false = b39)
    (h64 : ops.necessary ⟨⟨([2,1,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,1],[1]) = some [b750])
    (h33 : ops.pull (lowerHistoryH7) ([1,1,1],[1]) true = b835)
    (h34 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,1],[1]) true = b1090)
    (h35 : ops.pull (lowerHistoryHN) ([1,1,1],[1]) true = b39)
    : RootOps19.eval ops path1258 = ([[b371,b843,b433,b1162,b288,b812,b1151,b300,b745,b457,b10,b39,b750,b835,b1090,b39],[b371,b843,b433,b1162,b288,b812,b273,b838,b800,b1163,b300,b745,b457,b10,b39,b750,b835,b1090,b39]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1258, h0, h1, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h31, h64, h33, h34, h35, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1258 : lowerHistorySourcePremises path1258 = raw1258.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1258 RootOps19.actualOps bv10 bv39 bv273 bv288 bv300 bv371 bv433 bv457 bv745 bv750 bv800 bv812 bv835 bv838 bv843 bv1090 bv1151 bv1162 bv1163 op0 op1 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op46 op31 op64 op33 op34 op35
theorem dedup1258 : raw1258.map List.eraseDups = expected1258 := by
  decide +kernel
theorem source1258 : lowerHistorySourcePremises path1258 = expected1258 := (rawSource1258).trans (dedup1258)
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def src1258 : List (List Nat) := [[371,843,433,1162,288,812,1151,300,745,457,10,39,750,835,1090],[371,843,433,1162,288,812,273,838,800,1163,300,745,457,10,39,750,835,1090]]
theorem sourceIDs1258 : lowerHistorySourcePremises path1258 = src1258.map (List.map lowerHistoryBound) := by
  have hb : src1258.map (List.map lowerHistoryBound) = expected1258 := by
    simp only [src1258, expected1258, List.map_cons, List.map_nil, bound10, bound39, bound273, bound288, bound300, bound371, bound433, bound457, bound745, bound750, bound800, bound812, bound835, bound838, bound843, bound1090, bound1151, bound1162, bound1163]
  exact source1258.trans hb.symm
theorem length1258 : path1258.alternatives = (lowerHistorySourcePremises path1258).length := by
  rw [sourceIDs1258]
  rfl
theorem binding1258 : lowerHistoryPathBinding path1258 := by
  apply BindingIds19.pathBinding_from_ids path1258 src1258 [] recs1258 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1258 rfl records1258 rfl
  · intro r hr _
    simp only [recs1258, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise648)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise646)
  · intro r hr _
    simp only [recs1258, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1258] using witness518_projection
    · simpa only [blockWids, path1258] using witness518_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1258 recs1258 records1258 length1258 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def path1259 : LowerHistoryPath := ⟨.initial,173,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([1],[]),false)],([2,1,1,1],[3,1,3,1]),(true,true),false,2,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩
noncomputable def raw1259 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv455,bv29,bv198,bv455],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv455,bv29,bv198,bv455]]
noncomputable def expected1259 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv455,bv29,bv198],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv455,bv29,bv198]]
theorem structural1259 (ops : RootOps19.SourceOps) (b10 b29 b198 b273 b288 b300 b371 b433 b455 b457 b745 b800 b812 b838 b843 b1151 b1162 b1163 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h36 : ops.normalization ([1],[]) true false = b288)
    (h37 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([1],[]) = some [b812])
    (h38 : ops.pull (lowerHistoryH2) ([1],[]) true = b1151)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) true = b273)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) true = b838)
    (h41 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1],[]) true = b800)
    (h42 : ops.pull (lowerHistoryH23) ([1],[]) true = b1163)
    (h43 : ops.normalization ([1,1],[]) true true = b300)
    (h44 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1],[]) = some [b745])
    (h45 : ops.normalization ([1,1],[1]) false false = b457)
    (h46 : ops.necessary ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1],[1]) = some [b10])
    (h8 : ops.normalization ([1,1,1],[1]) false false = b455)
    (h65 : ops.necessary ⟨⟨([2,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,1],[1]) = some [b29])
    (h66 : ops.pull (lowerHistoryH7) ([1,1,1],[1]) false = b198)
    (h67 : ops.pull (lowerHistoryHN) ([1,1,1],[1]) false = b455)
    : RootOps19.eval ops path1259 = ([[b371,b843,b433,b1162,b288,b812,b1151,b300,b745,b457,b10,b455,b29,b198,b455],[b371,b843,b433,b1162,b288,b812,b273,b838,b800,b1163,b300,b745,b457,b10,b455,b29,b198,b455]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1259, h0, h1, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h8, h65, h66, h67, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1259 : lowerHistorySourcePremises path1259 = raw1259.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1259 RootOps19.actualOps bv10 bv29 bv198 bv273 bv288 bv300 bv371 bv433 bv455 bv457 bv745 bv800 bv812 bv838 bv843 bv1151 bv1162 bv1163 op0 op1 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op46 op8 op65 op66 op67
theorem dedup1259 : raw1259.map List.eraseDups = expected1259 := by
  decide +kernel
theorem source1259 : lowerHistorySourcePremises path1259 = expected1259 := (rawSource1259).trans (dedup1259)
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def src1259 : List (List Nat) := [[371,843,433,1162,288,812,1151,300,745,457,10,455,29,198],[371,843,433,1162,288,812,273,838,800,1163,300,745,457,10,455,29,198]]
theorem sourceIDs1259 : lowerHistorySourcePremises path1259 = src1259.map (List.map lowerHistoryBound) := by
  have hb : src1259.map (List.map lowerHistoryBound) = expected1259 := by
    simp only [src1259, expected1259, List.map_cons, List.map_nil, bound10, bound29, bound198, bound273, bound288, bound300, bound371, bound433, bound455, bound457, bound745, bound800, bound812, bound838, bound843, bound1151, bound1162, bound1163]
  exact source1259.trans hb.symm
theorem length1259 : path1259.alternatives = (lowerHistorySourcePremises path1259).length := by
  rw [sourceIDs1259]
  rfl
theorem binding1259 : lowerHistoryPathBinding path1259 := by
  apply BindingIds19.pathBinding_from_ids path1259 src1259 [] recs1259 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1259 rfl records1259 rfl
  · intro r hr _
    simp only [recs1259, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise640)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise638)
  · intro r hr _
    simp only [recs1259, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1259] using witness332_projection
    · simpa only [blockWids, path1259] using witness332_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1259 recs1259 records1259 length1259 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
open BindingNumeric20
theorem op68 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,1],[1]) false = bv1043 := by
  norm_num [bv1043, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op69 : lowerHistoryNormalization ([1,1,1,3],[1]) true true = bv310 := by
  norm_num [bv310, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op70 : lowerHistoryNecessary ⟨⟨([2,1,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,1,3],[1]) = some [bv562] := by
  decide +kernel
theorem op71 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,1,3],[1]) true = bv167 := by
  norm_num [bv167, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op72 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,1,3],[1]) true = bv605 := by
  norm_num [bv605, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op73 : lowerHistoryPull (lowerHistoryHN) ([1,1,1,3],[1]) true = bv33 := by
  norm_num [bv33, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def path1260 : LowerHistoryPath := ⟨.initial,174,[2],([1],[]),true,[(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([2,1,1,1,3],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,2⟩
noncomputable def raw1260 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv455,bv29,bv1043,bv310,bv562,bv167,bv605,bv33],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv455,bv29,bv1043,bv310,bv562,bv167,bv605,bv33]]
noncomputable def expected1260 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv288,bv812,bv1151,bv300,bv745,bv457,bv10,bv455,bv29,bv1043,bv310,bv562,bv167,bv605,bv33],[bv371,bv843,bv433,bv1162,bv288,bv812,bv273,bv838,bv800,bv1163,bv300,bv745,bv457,bv10,bv455,bv29,bv1043,bv310,bv562,bv167,bv605,bv33]]
theorem structural1260 (ops : RootOps19.SourceOps) (b10 b29 b33 b167 b273 b288 b300 b310 b371 b433 b455 b457 b562 b605 b745 b800 b812 b838 b843 b1043 b1151 b1162 b1163 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h36 : ops.normalization ([1],[]) true false = b288)
    (h37 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([1],[]) = some [b812])
    (h38 : ops.pull (lowerHistoryH2) ([1],[]) true = b1151)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) true = b273)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) true = b838)
    (h41 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1],[]) true = b800)
    (h42 : ops.pull (lowerHistoryH23) ([1],[]) true = b1163)
    (h43 : ops.normalization ([1,1],[]) true true = b300)
    (h44 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1],[]) = some [b745])
    (h45 : ops.normalization ([1,1],[1]) false false = b457)
    (h46 : ops.necessary ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1],[1]) = some [b10])
    (h8 : ops.normalization ([1,1,1],[1]) false false = b455)
    (h65 : ops.necessary ⟨⟨([2,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,1],[1]) = some [b29])
    (h68 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,1],[1]) false = b1043)
    (h69 : ops.normalization ([1,1,1,3],[1]) true true = b310)
    (h70 : ops.necessary ⟨⟨([2,1,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,1,3],[1]) = some [b562])
    (h71 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,1,3],[1]) true = b167)
    (h72 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,1,3],[1]) true = b605)
    (h73 : ops.pull (lowerHistoryHN) ([1,1,1,3],[1]) true = b33)
    : RootOps19.eval ops path1260 = ([[b371,b843,b433,b1162,b288,b812,b1151,b300,b745,b457,b10,b455,b29,b1043,b310,b562,b167,b605,b33],[b371,b843,b433,b1162,b288,b812,b273,b838,b800,b1163,b300,b745,b457,b10,b455,b29,b1043,b310,b562,b167,b605,b33]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,true,false,none⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hf0 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1260, h0, h1, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h8, h65, h68, h69, h70, h71, h72, h73, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1260 : lowerHistorySourcePremises path1260 = raw1260.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1260 RootOps19.actualOps bv10 bv29 bv33 bv167 bv273 bv288 bv300 bv310 bv371 bv433 bv455 bv457 bv562 bv605 bv745 bv800 bv812 bv838 bv843 bv1043 bv1151 bv1162 bv1163 op0 op1 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op46 op8 op65 op68 op69 op70 op71 op72 op73
theorem dedup1260 : raw1260.map List.eraseDups = expected1260 := by
  decide +kernel
theorem source1260 : lowerHistorySourcePremises path1260 = expected1260 := (rawSource1260).trans (dedup1260)
end M7ContinueSep17.Initial20260918.B1255_1260

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1255_1260
noncomputable def src1260 : List (List Nat) := [[371,843,433,1162,288,812,1151,300,745,457,10,455,29,1043,310,562,167,605,33],[371,843,433,1162,288,812,273,838,800,1163,300,745,457,10,455,29,1043,310,562,167,605,33]]
theorem sourceIDs1260 : lowerHistorySourcePremises path1260 = src1260.map (List.map lowerHistoryBound) := by
  have hb : src1260.map (List.map lowerHistoryBound) = expected1260 := by
    simp only [src1260, expected1260, List.map_cons, List.map_nil, bound10, bound29, bound33, bound167, bound273, bound288, bound300, bound310, bound371, bound433, bound455, bound457, bound562, bound605, bound745, bound800, bound812, bound838, bound843, bound1043, bound1151, bound1162, bound1163]
  exact source1260.trans hb.symm
theorem length1260 : path1260.alternatives = (lowerHistorySourcePremises path1260).length := by
  rw [sourceIDs1260]
  rfl
theorem binding1260 : lowerHistoryPathBinding path1260 := by
  apply BindingIds19.pathBinding_from_ids path1260 src1260 [] recs1260 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1260 rfl records1260 rfl
  · intro r hr _
    simp only [recs1260, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise600)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise598)
  · intro r hr _
    simp only [recs1260, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1260] using witness379_projection
    · simpa only [blockWids, path1260] using witness379_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1260 recs1260 records1260 length1260 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1255_1260

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
namespace M7ContinueSep17.Initial20260918.B1255_1260
theorem _root_.solution : lowerHistoryBindingBatch 1255 1260 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1255]? = some M7ContinueSep17.Initial20260918.B1255_1260.path1256 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 169 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1256
  · have hl : lowerHistoryPaths[1256]? = some M7ContinueSep17.Initial20260918.B1255_1260.path1257 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 170 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1257
  · have hl : lowerHistoryPaths[1257]? = some M7ContinueSep17.Initial20260918.B1255_1260.path1258 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 171 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1258
  · have hl : lowerHistoryPaths[1258]? = some M7ContinueSep17.Initial20260918.B1255_1260.path1259 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 172 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1259
  · have hl : lowerHistoryPaths[1259]? = some M7ContinueSep17.Initial20260918.B1255_1260.path1260 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 173 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1260
end M7ContinueSep17.Initial20260918.B1255_1260

#print axioms solution
