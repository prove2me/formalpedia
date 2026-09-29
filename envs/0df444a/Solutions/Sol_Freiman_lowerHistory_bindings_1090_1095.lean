-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1090_1095
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T05:21:04.464377+00:00
-- url     : https://prove2.me/submissions/6309796f-7254-4c37-bcd8-6ee749c48eb6

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
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def bv37 : CertBound := ⟨true,false,⟨⟨(-160951/1585298),(123103/1585298),(0),(0)⟩,⟨(185/241),(1/241),(0),(0)⟩,⟨(225/286),(-1/286),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv49 : CertBound := ⟨true,false,⟨⟨(-130297/2999821),(296548/8999463),(0),(0)⟩,⟨(611/781),(1/781),(0),(0)⟩,⟨(132/167),(-1/501),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv83 : CertBound := ⟨true,false,⟨⟨(-241/36490),(0),(0),(79/36490)⟩,⟨(1611/2050),(0),(0),(1/2050)⟩,⟨(145/178),(0),(0),(-1/178)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv85 : CertBound := ⟨true,false,⟨⟨(-1/170),(0),(0),(19/3570)⟩,⟨(37/50),(0),(0),(1/150)⟩,⟨(27/34),(0),(0),(-1/238)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv88 : CertBound := ⟨true,false,⟨⟨(-349/62834),(0),(0),(189/62834)⟩,⟨(551/706),(0),(0),(1/706)⟩,⟨(145/178),(0),(0),(-1/178)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv132 : CertBound := ⟨true,false,⟨⟨(133/21164),(324/5291),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv148 : CertBound := ⟨true,false,⟨⟨(28700400200/2875023092747),(943569500/8625069278241),(0),(0)⟩,⟨(16097/20423),(-1/61269),(0),(0)⟩,⟨(17754/22513),(1/22513),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv150 : CertBound := ⟨true,false,⟨⟨(9551131/783196700),(2818489/783196700),(0),(0)⟩,⟨(94/121),(1/121),(0),(0)⟩,⟨(607/766),(-1/766),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv240 : CertBound := ⟨true,false,⟨⟨(2093/16500),(161/4125),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv245 : CertBound := ⟨true,false,⟨⟨(25047/134000),(0),(0),(3243/938000)⟩,⟨(7/10),(0),(0),(1/70)⟩,⟨(519/670),(0),(0),(-1/670)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(119/202),(0),(0),(-1/202)⟩⟩⟩
noncomputable def bv261 : CertBound := ⟨true,false,⟨⟨(871317/2766500),(-100161/5533000),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩⟩⟩
noncomputable def bv280 : CertBound := ⟨true,false,⟨⟨(113/166),(0),(0),(-23/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(125/166),(0),(0),(1/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv342 : CertBound := ⟨true,true,⟨⟨(-241/36490),(0),(0),(79/36490)⟩,⟨(1611/2050),(0),(0),(1/2050)⟩,⟨(145/178),(0),(0),(-1/178)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv344 : CertBound := ⟨true,true,⟨⟨(-1/170),(0),(0),(19/3570)⟩,⟨(37/50),(0),(0),(1/150)⟩,⟨(27/34),(0),(0),(-1/238)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv347 : CertBound := ⟨true,true,⟨⟨(-349/62834),(0),(0),(189/62834)⟩,⟨(551/706),(0),(0),(1/706)⟩,⟨(145/178),(0),(0),(-1/178)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv433 : CertBound := ⟨true,true,⟨⟨(729/1024),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv446 : CertBound := ⟨false,false,⟨⟨(-2047/2171),(3668/6513),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(132/167),(-1/501),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv502 : CertBound := ⟨false,false,⟨⟨(147554/41703467),(263615/41703467),(0),(0)⟩,⟨(1277/1621),(1/1621),(0),(0)⟩,⟨(3121/3958),(-1/3958),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv506 : CertBound := ⟨false,false,⟨⟨(1548195/406284742),(797522/203142371),(0),(0)⟩,⟨(80792/102649),(1/102649),(0),(0)⟩,⟨(3121/3958),(-1/3958),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv526 : CertBound := ⟨false,false,⟨⟨(21813/3519191),(181489/10557573),(0),(0)⟩,⟨(1277/1621),(1/1621),(0),(0)⟩,⟨(132/167),(-1/501),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv571 : CertBound := ⟨false,false,⟨⟨(8973781000/737420266089),(34141000/81935585121),(0),(0)⟩,⟨(2466/3133),(1/3133),(0),(0)⟩,⟨(16097/20423),(-1/61269),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv586 : CertBound := ⟨false,false,⟨⟨(17809/1124747),(42240/1124747),(0),(0)⟩,⟨(185/241),(1/241),(0),(0)⟩,⟨(555/718),(-1/718),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv592 : CertBound := ⟨false,false,⟨⟨(147336300/8500012543),(-46246400/8500012543),(0),(0)⟩,⟨(8400/10657),(1/10657),(0),(0)⟩,⟨(1845/2339),(-1/7017),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv701 : CertBound := ⟨false,false,⟨⟨(15754/231803),(11763/231803),(0),(0)⟩,⟨(225/286),(-1/286),(0),(0)⟩,⟨(1277/1621),(1/1621),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv722 : CertBound := ⟨false,false,⟨⟨(26487300/277179463),(-8224400/277179463),(0),(0)⟩,⟨(462/599),(1/1797),(0),(0)⟩,⟨(1051/1357),(-1/1357),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv727 : CertBound := ⟨false,false,⟨⟨(25003083/251579900),(89651/251579900),(0),(0)⟩,⟨(185/241),(1/241),(0),(0)⟩,⟨(225/286),(-1/286),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩⟩⟩
noncomputable def bv777 : CertBound := ⟨false,false,⟨⟨(969900/4043237),(-305200/4043237),(0),(0)⟩,⟨(611/781),(1/781),(0),(0)⟩,⟨(132/167),(-1/501),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv799 : CertBound := ⟨false,false,⟨⟨(371/1100),(-1/220),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv830 : CertBound := ⟨false,false,⟨⟨(113/166),(0),(0),(-23/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(125/166),(0),(0),(1/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv832 : CertBound := ⟨false,false,⟨⟨(7/10),(0),(0),(-9/70)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(7/10),(0),(0),(1/70)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv839 : CertBound := ⟨false,false,⟨⟨(9/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv931 : CertBound := ⟨false,true,⟨⟨(161533/74780169),(105233/74780169),(0),(0)⟩,⟨(8400/10657),(1/10657),(0),(0)⟩,⟨(1845/2339),(-1/7017),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv978 : CertBound := ⟨false,true,⟨⟨(28700400200/2875023092747),(943569500/8625069278241),(0),(0)⟩,⟨(16097/20423),(-1/61269),(0),(0)⟩,⟨(17754/22513),(1/22513),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv981 : CertBound := ⟨false,true,⟨⟨(29443/2438529),(6381/812843),(0),(0)⟩,⟨(462/599),(1/1797),(0),(0)⟩,⟨(1051/1357),(-1/1357),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv982 : CertBound := ⟨false,true,⟨⟨(9551131/783196700),(2818489/783196700),(0),(0)⟩,⟨(94/121),(1/121),(0),(0)⟩,⟨(607/766),(-1/766),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv991 : CertBound := ⟨false,true,⟨⟨(11058644500/777685599353),(-2842500/5594860427),(0),(0)⟩,⟨(1277/1621),(1/1621),(0),(0)⟩,⟨(16097/20423),(-1/61269),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1030 : CertBound := ⟨false,true,⟨⟨(11659/391281),(2533/130427),(0),(0)⟩,⟨(611/781),(1/781),(0),(0)⟩,⟨(132/167),(-1/501),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1076 : CertBound := ⟨false,true,⟨⟨(809632611/13214548150),(312390999/132145481500),(0),(0)⟩,⟨(185/241),(1/241),(0),(0)⟩,⟨(7903/10249),(-1/10249),(0),(0)⟩,⟨(113/179),(1/537),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1115 : CertBound := ⟨false,true,⟨⟨(25047/134000),(0),(0),(3243/938000)⟩,⟨(7/10),(0),(0),(1/70)⟩,⟨(519/670),(0),(0),(-1/670)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(119/202),(0),(0),(-1/202)⟩⟩⟩
noncomputable def bv1140 : CertBound := ⟨false,true,⟨⟨(871317/2766500),(-100161/5533000),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩⟩⟩
noncomputable def bv1162 : CertBound := ⟨false,true,⟨⟨(225/289),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
open BindingNumeric20
theorem op138 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [bv371,bv843,bv433,bv1162] := by
  decide +kernel
theorem op139 : ([] : List CertBound) = [] := by
  decide +kernel
theorem op140 : lowerHistoryNormalization ([1],[]) false false = bv839 := by
  norm_num [bv839, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
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
theorem op159 : lowerHistoryNormalization ([1,3],[1]) false false = bv832 := by
  norm_num [bv832, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op160 : lowerHistoryNecessary ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([1,3],[1]) = some [bv37] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
open BindingNumeric20
theorem op164 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,3],[1]) false = bv727 := by
  norm_num [bv727, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op165 : lowerHistoryPull (lowerHistoryH5) ([1,3],[1]) false = bv1076 := by
  norm_num [bv1076, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op173 : lowerHistoryNormalization ([1,3,2],[1]) true true = bv344 := by
  norm_num [bv344, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op174 : lowerHistoryNecessary ⟨⟨([2,1,3,2],[3,1,3,1]),(true,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,3,2],[1]) = some [bv586] := by
  decide +kernel
theorem op175 : lowerHistoryPull (lowerHistoryH7) ([1,3,2],[1]) true = bv722 := by
  norm_num [bv722, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op176 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,3,2],[1]) true = bv981 := by
  norm_num [bv981, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op177 : lowerHistoryPull (lowerHistoryHN) ([1,3,2],[1]) true = bv85 := by
  norm_num [bv85, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op178 : lowerHistoryNormalization ([1,3,1],[1]) true false = bv280 := by
  norm_num [bv280, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op179 : lowerHistoryNecessary ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,3,1],[1]) = some [bv701] := by
  decide +kernel
theorem op156 : lowerHistoryPull (lowerHistoryH7) ([1,3,1],[1]) true = bv777 := by
  norm_num [bv777, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op157 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,3,1],[1]) true = bv1030 := by
  norm_num [bv1030, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op158 : lowerHistoryPull (lowerHistoryHN) ([1,3,1],[1]) true = bv280 := by
  norm_num [bv280, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def path1091 : LowerHistoryPath := ⟨.initial,5,[2],([1],[]),false,[(([3],[1]),false),(([2],[]),true)],([2,1,3,2],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩
noncomputable def raw1091 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv727,bv1076,bv344,bv586,bv722,bv981,bv85],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv727,bv1076,bv344,bv586,bv722,bv981,bv85],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv727,bv1076,bv344,bv586,bv722,bv981,bv85]]
noncomputable def expected1091 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv727,bv1076,bv344,bv586,bv722,bv981,bv85],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv727,bv1076,bv344,bv586,bv722,bv981,bv85],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv727,bv1076,bv344,bv586,bv722,bv981,bv85]]
theorem structural1091 (ops : RootOps19.SourceOps) (b37 b85 b132 b240 b245 b261 b344 b371 b433 b586 b722 b727 b799 b832 b839 b843 b981 b1076 b1115 b1140 b1162 : CertBound)
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
    (h173 : ops.normalization ([1,3,2],[1]) true true = b344)
    (h174 : ops.necessary ⟨⟨([2,1,3,2],[3,1,3,1]),(true,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,3,2],[1]) = some [b586])
    (h175 : ops.pull (lowerHistoryH7) ([1,3,2],[1]) true = b722)
    (h176 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,3,2],[1]) true = b981)
    (h177 : ops.pull (lowerHistoryHN) ([1,3,2],[1]) true = b85)
    : RootOps19.eval ops path1091 = ([[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b727,b1076,b344,b586,b722,b981,b85],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b727,b1076,b344,b586,b722,b981,b85],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b727,b1076,b344,b586,b722,b981,b85]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1091, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h159, h160, h164, h165, h173, h174, h175, h176, h177, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1091 : lowerHistorySourcePremises path1091 = raw1091.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1091 RootOps19.actualOps bv37 bv85 bv132 bv240 bv245 bv261 bv344 bv371 bv433 bv586 bv722 bv727 bv799 bv832 bv839 bv843 bv981 bv1076 bv1115 bv1140 bv1162 op138 op139 op140 op141 op142 op143 op144 op145 op146 op147 op159 op160 op164 op165 op173 op174 op175 op176 op177
theorem dedup1091 : raw1091.map List.eraseDups = expected1091 := by
  decide +kernel
theorem source1091 : lowerHistorySourcePremises path1091 = expected1091 := (rawSource1091).trans (dedup1091)
end M7ContinueSep17.Initial20260918.B1090_1095

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
namespace M7ContinueSep17.Initial20260918.B1090_1095
theorem bound37 : lowerHistoryBound 37 = bv37 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[36]? = some bv37 := Eq.refl (some bv37)
  exact (BoundCompact16.global_to_chunk1 36 (by decide)).trans hl
theorem bound49 : lowerHistoryBound 49 = bv49 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[48]? = some bv49 := Eq.refl (some bv49)
  exact (BoundCompact16.global_to_chunk1 48 (by decide)).trans hl
theorem bound83 : lowerHistoryBound 83 = bv83 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[82]? = some bv83 := Eq.refl (some bv83)
  exact (BoundCompact16.global_to_chunk1 82 (by decide)).trans hl
theorem bound85 : lowerHistoryBound 85 = bv85 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[84]? = some bv85 := Eq.refl (some bv85)
  exact (BoundCompact16.global_to_chunk1 84 (by decide)).trans hl
theorem bound88 : lowerHistoryBound 88 = bv88 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[87]? = some bv88 := Eq.refl (some bv88)
  exact (BoundCompact16.global_to_chunk1 87 (by decide)).trans hl
theorem bound132 : lowerHistoryBound 132 = bv132 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[131]? = some bv132 := Eq.refl (some bv132)
  exact (BoundCompact16.global_to_chunk1 131 (by decide)).trans hl
theorem bound148 : lowerHistoryBound 148 = bv148 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[147]? = some bv148 := Eq.refl (some bv148)
  exact (BoundCompact16.global_to_chunk1 147 (by decide)).trans hl
theorem bound150 : lowerHistoryBound 150 = bv150 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[149]? = some bv150 := Eq.refl (some bv150)
  exact (BoundCompact16.global_to_chunk1 149 (by decide)).trans hl
theorem bound240 : lowerHistoryBound 240 = bv240 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[39]? = some bv240 := Eq.refl (some bv240)
  exact (BoundCompact16.global_to_chunk2 39 (by decide)).trans hl
theorem bound245 : lowerHistoryBound 245 = bv245 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[44]? = some bv245 := Eq.refl (some bv245)
  exact (BoundCompact16.global_to_chunk2 44 (by decide)).trans hl
theorem bound261 : lowerHistoryBound 261 = bv261 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[60]? = some bv261 := Eq.refl (some bv261)
  exact (BoundCompact16.global_to_chunk2 60 (by decide)).trans hl
theorem bound280 : lowerHistoryBound 280 = bv280 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[79]? = some bv280 := Eq.refl (some bv280)
  exact (BoundCompact16.global_to_chunk2 79 (by decide)).trans hl
theorem bound342 : lowerHistoryBound 342 = bv342 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[141]? = some bv342 := Eq.refl (some bv342)
  exact (BoundCompact16.global_to_chunk2 141 (by decide)).trans hl
theorem bound344 : lowerHistoryBound 344 = bv344 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[143]? = some bv344 := Eq.refl (some bv344)
  exact (BoundCompact16.global_to_chunk2 143 (by decide)).trans hl
theorem bound347 : lowerHistoryBound 347 = bv347 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[146]? = some bv347 := Eq.refl (some bv347)
  exact (BoundCompact16.global_to_chunk2 146 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound433 : lowerHistoryBound 433 = bv433 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[32]? = some bv433 := Eq.refl (some bv433)
  exact (BoundCompact16.global_to_chunk3 32 (by decide)).trans hl
theorem bound446 : lowerHistoryBound 446 = bv446 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[45]? = some bv446 := Eq.refl (some bv446)
  exact (BoundCompact16.global_to_chunk3 45 (by decide)).trans hl
theorem bound502 : lowerHistoryBound 502 = bv502 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[101]? = some bv502 := Eq.refl (some bv502)
  exact (BoundCompact16.global_to_chunk3 101 (by decide)).trans hl
theorem bound506 : lowerHistoryBound 506 = bv506 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[105]? = some bv506 := Eq.refl (some bv506)
  exact (BoundCompact16.global_to_chunk3 105 (by decide)).trans hl
theorem bound526 : lowerHistoryBound 526 = bv526 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[125]? = some bv526 := Eq.refl (some bv526)
  exact (BoundCompact16.global_to_chunk3 125 (by decide)).trans hl
theorem bound571 : lowerHistoryBound 571 = bv571 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[170]? = some bv571 := Eq.refl (some bv571)
  exact (BoundCompact16.global_to_chunk3 170 (by decide)).trans hl
theorem bound586 : lowerHistoryBound 586 = bv586 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[185]? = some bv586 := Eq.refl (some bv586)
  exact (BoundCompact16.global_to_chunk3 185 (by decide)).trans hl
theorem bound592 : lowerHistoryBound 592 = bv592 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[191]? = some bv592 := Eq.refl (some bv592)
  exact (BoundCompact16.global_to_chunk3 191 (by decide)).trans hl
theorem bound701 : lowerHistoryBound 701 = bv701 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[100]? = some bv701 := Eq.refl (some bv701)
  exact (BoundCompact16.global_to_chunk4 100 (by decide)).trans hl
theorem bound722 : lowerHistoryBound 722 = bv722 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[121]? = some bv722 := Eq.refl (some bv722)
  exact (BoundCompact16.global_to_chunk4 121 (by decide)).trans hl
theorem bound727 : lowerHistoryBound 727 = bv727 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[126]? = some bv727 := Eq.refl (some bv727)
  exact (BoundCompact16.global_to_chunk4 126 (by decide)).trans hl
theorem bound777 : lowerHistoryBound 777 = bv777 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[176]? = some bv777 := Eq.refl (some bv777)
  exact (BoundCompact16.global_to_chunk4 176 (by decide)).trans hl
theorem bound799 : lowerHistoryBound 799 = bv799 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[198]? = some bv799 := Eq.refl (some bv799)
  exact (BoundCompact16.global_to_chunk4 198 (by decide)).trans hl
theorem bound830 : lowerHistoryBound 830 = bv830 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[29]? = some bv830 := Eq.refl (some bv830)
  exact (BoundCompact16.global_to_chunk5 29 (by decide)).trans hl
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
theorem bound931 : lowerHistoryBound 931 = bv931 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[130]? = some bv931 := Eq.refl (some bv931)
  exact (BoundCompact16.global_to_chunk5 130 (by decide)).trans hl
theorem bound978 : lowerHistoryBound 978 = bv978 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[177]? = some bv978 := Eq.refl (some bv978)
  exact (BoundCompact16.global_to_chunk5 177 (by decide)).trans hl
theorem bound981 : lowerHistoryBound 981 = bv981 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[180]? = some bv981 := Eq.refl (some bv981)
  exact (BoundCompact16.global_to_chunk5 180 (by decide)).trans hl
theorem bound982 : lowerHistoryBound 982 = bv982 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[181]? = some bv982 := Eq.refl (some bv982)
  exact (BoundCompact16.global_to_chunk5 181 (by decide)).trans hl
theorem bound991 : lowerHistoryBound 991 = bv991 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[190]? = some bv991 := Eq.refl (some bv991)
  exact (BoundCompact16.global_to_chunk5 190 (by decide)).trans hl
theorem bound1030 : lowerHistoryBound 1030 = bv1030 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[29]? = some bv1030 := Eq.refl (some bv1030)
  exact (BoundCompact16.global_to_chunk6 29).trans hl
theorem bound1076 : lowerHistoryBound 1076 = bv1076 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[75]? = some bv1076 := Eq.refl (some bv1076)
  exact (BoundCompact16.global_to_chunk6 75).trans hl
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
end M7ContinueSep17.Initial20260918.B1090_1095

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
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def recs1091 : List LowerHistoryRecord := [⟨.initial,5,0,(-1),false,826,489⟩,⟨.initial,5,1,(-1),false,825,489⟩,⟨.initial,5,2,(-1),false,827,489⟩]
theorem records1091 : lowerHistoryRecordsFor (⟨.initial,5,[2],([1],[]),false,[(([3],[1]),false),(([2],[]),true)],([2,1,3,2],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩ : LowerHistoryPath) = recs1091 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 5)) = recs1091
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1092 : List LowerHistoryRecord := [⟨.initial,6,0,(-1),false,834,504⟩,⟨.initial,6,1,(-1),false,833,504⟩,⟨.initial,6,2,(-1),false,835,504⟩]
theorem records1092 : lowerHistoryRecordsFor (⟨.initial,6,[2],([1],[]),false,[(([3],[1]),false),(([1],[]),true)],([2,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩ : LowerHistoryPath) = recs1092 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 6)) = recs1092
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1093 : List LowerHistoryRecord := [⟨.initial,7,0,(-1),false,818,421⟩,⟨.initial,7,1,(-1),false,817,421⟩,⟨.initial,7,2,(-1),false,819,421⟩]
theorem records1093 : lowerHistoryRecordsFor (⟨.initial,7,[2],([1],[]),false,[(([3],[1]),false),(([1],[]),false)],([2,1,3,1],[3,1,3,1]),(true,true),false,2,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩ : LowerHistoryPath) = recs1093 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 7)) = recs1093
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1094 : List LowerHistoryRecord := [⟨.initial,8,0,(-1),false,802,369⟩,⟨.initial,8,1,(-1),false,798,369⟩,⟨.initial,8,2,(-1),false,801,369⟩,⟨.initial,8,3,(-1),false,797,369⟩,⟨.initial,8,4,(-1),false,803,369⟩,⟨.initial,8,5,(-1),false,799,369⟩]
theorem records1094 : lowerHistoryRecordsFor (⟨.initial,8,[2],([1],[]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([2,1,3,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,6⟩ : LowerHistoryPath) = recs1094 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 8)) = recs1094
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1095 : List LowerHistoryRecord := [⟨.initial,9,0,(-1),false,794,454⟩,⟨.initial,9,1,(-1),false,786,454⟩,⟨.initial,9,2,(-1),false,790,454⟩,⟨.initial,9,3,(-1),false,782,454⟩,⟨.initial,9,4,(-1),false,793,454⟩,⟨.initial,9,5,(-1),false,785,454⟩,⟨.initial,9,6,(-1),false,789,454⟩,⟨.initial,9,7,(-1),false,781,454⟩,⟨.initial,9,8,(-1),false,795,454⟩,⟨.initial,9,9,(-1),false,787,454⟩,⟨.initial,9,10,(-1),false,791,454⟩,⟨.initial,9,11,(-1),false,783,454⟩]
theorem records1095 : lowerHistoryRecordsFor (⟨.initial,9,[2],([1],[]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,1,3,1,2,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,12⟩ : LowerHistoryPath) = recs1095 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 9)) = recs1095
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
end M7ContinueSep17.Initial20260918.B1090_1095

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
namespace M7ContinueSep17.Initial20260918.B1090_1095
theorem premise781 : lowerHistoryPremises[780]? = some ([37,49,83,132,148,150,240,342,347,371,433,446,502,506,526,571,592,799,830,832,839,843,931,991,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[780]? = lowerHistoryPremises04[180]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 180 (by decide)
  exact hg.trans (by rfl)
theorem premise782 : lowerHistoryPremises[781]? = some ([37,49,83,132,148,150,245,342,347,371,433,446,502,506,526,571,592,799,830,832,839,843,931,991,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[781]? = lowerHistoryPremises04[181]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 181 (by decide)
  exact hg.trans (by rfl)
theorem premise783 : lowerHistoryPremises[782]? = some ([37,49,83,132,148,150,261,342,347,371,433,446,502,506,526,571,592,799,830,832,839,843,931,991,1162] : List Nat) := by
  have hg : lowerHistoryPremises[782]? = lowerHistoryPremises04[182]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 182 (by decide)
  exact hg.trans (by rfl)
theorem premise785 : lowerHistoryPremises[784]? = some ([37,49,83,132,148,240,342,347,371,433,502,506,526,571,592,799,830,832,839,843,931,982,991,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[784]? = lowerHistoryPremises04[184]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 184 (by decide)
  exact hg.trans (by rfl)
theorem premise786 : lowerHistoryPremises[785]? = some ([37,49,83,132,148,245,342,347,371,433,502,506,526,571,592,799,830,832,839,843,931,982,991,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[785]? = lowerHistoryPremises04[185]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 185 (by decide)
  exact hg.trans (by rfl)
theorem premise787 : lowerHistoryPremises[786]? = some ([37,49,83,132,148,261,342,347,371,433,502,506,526,571,592,799,830,832,839,843,931,982,991,1162] : List Nat) := by
  have hg : lowerHistoryPremises[786]? = lowerHistoryPremises04[186]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 186 (by decide)
  exact hg.trans (by rfl)
theorem premise789 : lowerHistoryPremises[788]? = some ([37,49,83,132,150,240,342,347,371,433,446,502,526,592,799,830,832,839,843,931,978,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[788]? = lowerHistoryPremises04[188]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 188 (by decide)
  exact hg.trans (by rfl)
theorem premise790 : lowerHistoryPremises[789]? = some ([37,49,83,132,150,245,342,347,371,433,446,502,526,592,799,830,832,839,843,931,978,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[789]? = lowerHistoryPremises04[189]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 189 (by decide)
  exact hg.trans (by rfl)
theorem premise791 : lowerHistoryPremises[790]? = some ([37,49,83,132,150,261,342,347,371,433,446,502,526,592,799,830,832,839,843,931,978,1162] : List Nat) := by
  have hg : lowerHistoryPremises[790]? = lowerHistoryPremises04[190]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 190 (by decide)
  exact hg.trans (by rfl)
theorem premise793 : lowerHistoryPremises[792]? = some ([37,49,83,132,240,342,347,371,433,502,526,592,799,830,832,839,843,931,978,982,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[792]? = lowerHistoryPremises04[192]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 192 (by decide)
  exact hg.trans (by rfl)
theorem premise794 : lowerHistoryPremises[793]? = some ([37,49,83,132,245,342,347,371,433,502,526,592,799,830,832,839,843,931,978,982,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[793]? = lowerHistoryPremises04[193]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 193 (by decide)
  exact hg.trans (by rfl)
theorem premise795 : lowerHistoryPremises[794]? = some ([37,49,83,132,261,342,347,371,433,502,526,592,799,830,832,839,843,931,978,982,1162] : List Nat) := by
  have hg : lowerHistoryPremises[794]? = lowerHistoryPremises04[194]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 194 (by decide)
  exact hg.trans (by rfl)
theorem premise797 : lowerHistoryPremises[796]? = some ([37,49,88,132,148,150,240,347,371,433,446,526,571,799,830,832,839,843,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[796]? = lowerHistoryPremises04[196]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 196 (by decide)
  exact hg.trans (by rfl)
theorem premise798 : lowerHistoryPremises[797]? = some ([37,49,88,132,148,150,245,347,371,433,446,526,571,799,830,832,839,843,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[797]? = lowerHistoryPremises04[197]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 197 (by decide)
  exact hg.trans (by rfl)
theorem premise799 : lowerHistoryPremises[798]? = some ([37,49,88,132,148,150,261,347,371,433,446,526,571,799,830,832,839,843,1162] : List Nat) := by
  have hg : lowerHistoryPremises[798]? = lowerHistoryPremises04[198]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 198 (by decide)
  exact hg.trans (by rfl)
theorem premise801 : lowerHistoryPremises[800]? = some ([37,49,88,132,148,240,347,371,433,526,571,799,830,832,839,843,982,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[800]? = lowerHistoryPremises05[0]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 0 (by decide)
  exact hg.trans (by rfl)
theorem premise802 : lowerHistoryPremises[801]? = some ([37,49,88,132,148,245,347,371,433,526,571,799,830,832,839,843,982,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[801]? = lowerHistoryPremises05[1]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 1 (by decide)
  exact hg.trans (by rfl)
theorem premise803 : lowerHistoryPremises[802]? = some ([37,49,88,132,148,261,347,371,433,526,571,799,830,832,839,843,982,1162] : List Nat) := by
  have hg : lowerHistoryPremises[802]? = lowerHistoryPremises05[2]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 2 (by decide)
  exact hg.trans (by rfl)
theorem premise817 : lowerHistoryPremises[816]? = some ([37,49,132,150,240,371,433,799,830,832,839,843,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[816]? = lowerHistoryPremises05[16]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 16 (by decide)
  exact hg.trans (by rfl)
theorem premise818 : lowerHistoryPremises[817]? = some ([37,49,132,150,245,371,433,799,830,832,839,843,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[817]? = lowerHistoryPremises05[17]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 17 (by decide)
  exact hg.trans (by rfl)
theorem premise819 : lowerHistoryPremises[818]? = some ([37,49,132,150,261,371,433,799,830,832,839,843,1162] : List Nat) := by
  have hg : lowerHistoryPremises[818]? = lowerHistoryPremises05[18]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 18 (by decide)
  exact hg.trans (by rfl)
theorem premise825 : lowerHistoryPremises[824]? = some ([37,85,132,240,344,371,433,586,722,727,799,832,839,843,981,1076,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[824]? = lowerHistoryPremises05[24]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 24 (by decide)
  exact hg.trans (by rfl)
theorem premise826 : lowerHistoryPremises[825]? = some ([37,85,132,245,344,371,433,586,722,727,799,832,839,843,981,1076,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[825]? = lowerHistoryPremises05[25]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 25 (by decide)
  exact hg.trans (by rfl)
theorem premise827 : lowerHistoryPremises[826]? = some ([37,85,132,261,344,371,433,586,722,727,799,832,839,843,981,1076,1162] : List Nat) := by
  have hg : lowerHistoryPremises[826]? = lowerHistoryPremises05[26]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 26 (by decide)
  exact hg.trans (by rfl)
theorem premise833 : lowerHistoryPremises[832]? = some ([37,132,240,280,371,433,701,777,799,832,839,843,1030,1115,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[832]? = lowerHistoryPremises05[32]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 32 (by decide)
  exact hg.trans (by rfl)
theorem premise834 : lowerHistoryPremises[833]? = some ([37,132,245,280,371,433,701,777,799,832,839,843,1030,1140,1162] : List Nat) := by
  have hg : lowerHistoryPremises[833]? = lowerHistoryPremises05[33]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 33 (by decide)
  exact hg.trans (by rfl)
theorem premise835 : lowerHistoryPremises[834]? = some ([37,132,261,280,371,433,701,777,799,832,839,843,1030,1162] : List Nat) := by
  have hg : lowerHistoryPremises[834]? = lowerHistoryPremises05[34]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 34 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1090_1095
theorem witness369_projection : (lowerHistoryWitness 369).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 369).upperBound = lowerHistoryBound 571 ∧ (lowerHistoryWitness 369).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[168]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 571, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 571, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[368]? = lowerHistoryWitnesses02[168]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 168 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness421_projection : (lowerHistoryWitness 421).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 421).upperBound = lowerHistoryBound 830 ∧ (lowerHistoryWitness 421).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[20]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 830, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 830, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[420]? = lowerHistoryWitnesses03[20]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 20 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness454_projection : (lowerHistoryWitness 454).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 454).upperBound = lowerHistoryBound 931 ∧ (lowerHistoryWitness 454).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[53]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 931, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 931, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[453]? = lowerHistoryWitnesses03[53]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 53 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness489_projection : (lowerHistoryWitness 489).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 489).upperBound = lowerHistoryBound 981 ∧ (lowerHistoryWitness 489).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[88]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 981, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 981, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[488]? = lowerHistoryWitnesses03[88]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 88 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness504_projection : (lowerHistoryWitness 504).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 504).upperBound = lowerHistoryBound 1030 ∧ (lowerHistoryWitness 504).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[103]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 1030, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 1030, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[503]? = lowerHistoryWitnesses03[103]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 103 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 369 => (433,571)
  | 421 => (433,830)
  | 454 => (433,931)
  | 489 => (433,981)
  | 504 => (433,1030)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 781 => [37,49,83,132,148,150,240,342,347,371,433,446,502,506,526,571,592,799,830,832,839,843,931,991,1115,1140,1162]
  | 782 => [37,49,83,132,148,150,245,342,347,371,433,446,502,506,526,571,592,799,830,832,839,843,931,991,1140,1162]
  | 783 => [37,49,83,132,148,150,261,342,347,371,433,446,502,506,526,571,592,799,830,832,839,843,931,991,1162]
  | 785 => [37,49,83,132,148,240,342,347,371,433,502,506,526,571,592,799,830,832,839,843,931,982,991,1115,1140,1162]
  | 786 => [37,49,83,132,148,245,342,347,371,433,502,506,526,571,592,799,830,832,839,843,931,982,991,1140,1162]
  | 787 => [37,49,83,132,148,261,342,347,371,433,502,506,526,571,592,799,830,832,839,843,931,982,991,1162]
  | 789 => [37,49,83,132,150,240,342,347,371,433,446,502,526,592,799,830,832,839,843,931,978,1115,1140,1162]
  | 790 => [37,49,83,132,150,245,342,347,371,433,446,502,526,592,799,830,832,839,843,931,978,1140,1162]
  | 791 => [37,49,83,132,150,261,342,347,371,433,446,502,526,592,799,830,832,839,843,931,978,1162]
  | 793 => [37,49,83,132,240,342,347,371,433,502,526,592,799,830,832,839,843,931,978,982,1115,1140,1162]
  | 794 => [37,49,83,132,245,342,347,371,433,502,526,592,799,830,832,839,843,931,978,982,1140,1162]
  | 795 => [37,49,83,132,261,342,347,371,433,502,526,592,799,830,832,839,843,931,978,982,1162]
  | 797 => [37,49,88,132,148,150,240,347,371,433,446,526,571,799,830,832,839,843,1115,1140,1162]
  | 798 => [37,49,88,132,148,150,245,347,371,433,446,526,571,799,830,832,839,843,1140,1162]
  | 799 => [37,49,88,132,148,150,261,347,371,433,446,526,571,799,830,832,839,843,1162]
  | 801 => [37,49,88,132,148,240,347,371,433,526,571,799,830,832,839,843,982,1115,1140,1162]
  | 802 => [37,49,88,132,148,245,347,371,433,526,571,799,830,832,839,843,982,1140,1162]
  | 803 => [37,49,88,132,148,261,347,371,433,526,571,799,830,832,839,843,982,1162]
  | 817 => [37,49,132,150,240,371,433,799,830,832,839,843,1115,1140,1162]
  | 818 => [37,49,132,150,245,371,433,799,830,832,839,843,1140,1162]
  | 819 => [37,49,132,150,261,371,433,799,830,832,839,843,1162]
  | 825 => [37,85,132,240,344,371,433,586,722,727,799,832,839,843,981,1076,1115,1140,1162]
  | 826 => [37,85,132,245,344,371,433,586,722,727,799,832,839,843,981,1076,1140,1162]
  | 827 => [37,85,132,261,344,371,433,586,722,727,799,832,839,843,981,1076,1162]
  | 833 => [37,132,240,280,371,433,701,777,799,832,839,843,1030,1115,1140,1162]
  | 834 => [37,132,245,280,371,433,701,777,799,832,839,843,1030,1140,1162]
  | 835 => [37,132,261,280,371,433,701,777,799,832,839,843,1030,1162]
  | _ => []
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def src1091 : List (List Nat) := [[371,843,433,1162,839,132,799,1140,245,832,37,727,1076,344,586,722,981,85],[371,843,433,1162,839,132,799,1140,1115,240,832,37,727,1076,344,586,722,981,85],[371,843,433,1162,839,132,799,261,832,37,727,1076,344,586,722,981,85]]
theorem sourceIDs1091 : lowerHistorySourcePremises path1091 = src1091.map (List.map lowerHistoryBound) := by
  have hb : src1091.map (List.map lowerHistoryBound) = expected1091 := by
    simp only [src1091, expected1091, List.map_cons, List.map_nil, bound37, bound85, bound132, bound240, bound245, bound261, bound344, bound371, bound433, bound586, bound722, bound727, bound799, bound832, bound839, bound843, bound981, bound1076, bound1115, bound1140, bound1162]
  exact source1091.trans hb.symm
theorem length1091 : path1091.alternatives = (lowerHistorySourcePremises path1091).length := by
  rw [sourceIDs1091]
  rfl
theorem binding1091 : lowerHistoryPathBinding path1091 := by
  apply BindingIds19.pathBinding_from_ids path1091 src1091 [] recs1091 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1091 rfl records1091 rfl
  · intro r hr _
    simp only [recs1091, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise826)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise825)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise827)
  · intro r hr _
    simp only [recs1091, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockWids, path1091] using witness489_projection
    · simpa only [blockWids, path1091] using witness489_projection
    · simpa only [blockWids, path1091] using witness489_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1091 recs1091 records1091 length1091 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def path1092 : LowerHistoryPath := ⟨.initial,6,[2],([1],[]),false,[(([3],[1]),false),(([1],[]),true)],([2,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩
noncomputable def raw1092 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv280,bv701,bv777,bv1030,bv280],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv280,bv701,bv777,bv1030,bv280],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv280,bv701,bv777,bv1030,bv280]]
noncomputable def expected1092 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv280,bv701,bv777,bv1030],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv280,bv701,bv777,bv1030],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv280,bv701,bv777,bv1030]]
theorem structural1092 (ops : RootOps19.SourceOps) (b37 b132 b240 b245 b261 b280 b371 b433 b701 b777 b799 b832 b839 b843 b1030 b1115 b1140 b1162 : CertBound)
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
    (h178 : ops.normalization ([1,3,1],[1]) true false = b280)
    (h179 : ops.necessary ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,3,1],[1]) = some [b701])
    (h156 : ops.pull (lowerHistoryH7) ([1,3,1],[1]) true = b777)
    (h157 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,3,1],[1]) true = b1030)
    (h158 : ops.pull (lowerHistoryHN) ([1,3,1],[1]) true = b280)
    : RootOps19.eval ops path1092 = ([[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b280,b701,b777,b1030,b280],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b280,b701,b777,b1030,b280],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b280,b701,b777,b1030,b280]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1092, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h159, h160, h178, h179, h156, h157, h158, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1092 : lowerHistorySourcePremises path1092 = raw1092.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1092 RootOps19.actualOps bv37 bv132 bv240 bv245 bv261 bv280 bv371 bv433 bv701 bv777 bv799 bv832 bv839 bv843 bv1030 bv1115 bv1140 bv1162 op138 op139 op140 op141 op142 op143 op144 op145 op146 op147 op159 op160 op178 op179 op156 op157 op158
theorem dedup1092 : raw1092.map List.eraseDups = expected1092 := by
  decide +kernel
theorem source1092 : lowerHistorySourcePremises path1092 = expected1092 := (rawSource1092).trans (dedup1092)
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def src1092 : List (List Nat) := [[371,843,433,1162,839,132,799,1140,245,832,37,280,701,777,1030],[371,843,433,1162,839,132,799,1140,1115,240,832,37,280,701,777,1030],[371,843,433,1162,839,132,799,261,832,37,280,701,777,1030]]
theorem sourceIDs1092 : lowerHistorySourcePremises path1092 = src1092.map (List.map lowerHistoryBound) := by
  have hb : src1092.map (List.map lowerHistoryBound) = expected1092 := by
    simp only [src1092, expected1092, List.map_cons, List.map_nil, bound37, bound132, bound240, bound245, bound261, bound280, bound371, bound433, bound701, bound777, bound799, bound832, bound839, bound843, bound1030, bound1115, bound1140, bound1162]
  exact source1092.trans hb.symm
theorem length1092 : path1092.alternatives = (lowerHistorySourcePremises path1092).length := by
  rw [sourceIDs1092]
  rfl
theorem binding1092 : lowerHistoryPathBinding path1092 := by
  apply BindingIds19.pathBinding_from_ids path1092 src1092 [] recs1092 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1092 rfl records1092 rfl
  · intro r hr _
    simp only [recs1092, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise834)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise833)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise835)
  · intro r hr _
    simp only [recs1092, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockWids, path1092] using witness504_projection
    · simpa only [blockWids, path1092] using witness504_projection
    · simpa only [blockWids, path1092] using witness504_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1092 recs1092 records1092 length1092 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
open BindingNumeric20
theorem op180 : lowerHistoryNormalization ([1,3,1],[1]) false false = bv830 := by
  norm_num [bv830, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op181 : lowerHistoryNecessary ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,3,1],[1]) = some [bv49] := by
  decide +kernel
theorem op182 : lowerHistoryPull (lowerHistoryH7) ([1,3,1],[1]) false = bv150 := by
  norm_num [bv150, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op183 : lowerHistoryPull (lowerHistoryHN) ([1,3,1],[1]) false = bv830 := by
  norm_num [bv830, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op184 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([1,3,1],[1]) false = bv982 := by
  norm_num [bv982, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op185 : lowerHistoryPull (lowerHistoryH9) ([1,3,1],[1]) false = bv446 := by
  norm_num [bv446, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op186 : lowerHistoryNormalization ([1,3,1,2],[1]) true true = bv347 := by
  norm_num [bv347, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op187 : lowerHistoryNecessary ⟨⟨([2,1,3,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,3,1,2],[1]) = some [bv526] := by
  decide +kernel
theorem op188 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,3,1,2],[1]) true = bv148 := by
  norm_num [bv148, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op189 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,3,1,2],[1]) true = bv571 := by
  norm_num [bv571, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op190 : lowerHistoryPull (lowerHistoryHN) ([1,3,1,2],[1]) true = bv88 := by
  norm_num [bv88, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op191 : lowerHistoryPull (lowerHistoryH2) ([1,3,1,2],[1]) true = bv978 := by
  norm_num [bv978, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def path1093 : LowerHistoryPath := ⟨.initial,7,[2],([1],[]),false,[(([3],[1]),false),(([1],[]),false)],([2,1,3,1],[3,1,3,1]),(true,true),false,2,⟨(1/3),(9/25),(5/19),(4/15)⟩,3⟩
noncomputable def raw1093 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv150,bv830],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv150,bv830],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv150,bv830]]
noncomputable def expected1093 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv150],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv150],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv150]]
theorem structural1093 (ops : RootOps19.SourceOps) (b37 b49 b132 b150 b240 b245 b261 b371 b433 b799 b830 b832 b839 b843 b1115 b1140 b1162 : CertBound)
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
    (h180 : ops.normalization ([1,3,1],[1]) false false = b830)
    (h181 : ops.necessary ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,3,1],[1]) = some [b49])
    (h182 : ops.pull (lowerHistoryH7) ([1,3,1],[1]) false = b150)
    (h183 : ops.pull (lowerHistoryHN) ([1,3,1],[1]) false = b830)
    : RootOps19.eval ops path1093 = ([[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b830,b49,b150,b830],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b830,b49,b150,b830],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b830,b49,b150,b830]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1093, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h159, h160, h180, h181, h182, h183, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1093 : lowerHistorySourcePremises path1093 = raw1093.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1093 RootOps19.actualOps bv37 bv49 bv132 bv150 bv240 bv245 bv261 bv371 bv433 bv799 bv830 bv832 bv839 bv843 bv1115 bv1140 bv1162 op138 op139 op140 op141 op142 op143 op144 op145 op146 op147 op159 op160 op180 op181 op182 op183
theorem dedup1093 : raw1093.map List.eraseDups = expected1093 := by
  decide +kernel
theorem source1093 : lowerHistorySourcePremises path1093 = expected1093 := (rawSource1093).trans (dedup1093)
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def src1093 : List (List Nat) := [[371,843,433,1162,839,132,799,1140,245,832,37,830,49,150],[371,843,433,1162,839,132,799,1140,1115,240,832,37,830,49,150],[371,843,433,1162,839,132,799,261,832,37,830,49,150]]
theorem sourceIDs1093 : lowerHistorySourcePremises path1093 = src1093.map (List.map lowerHistoryBound) := by
  have hb : src1093.map (List.map lowerHistoryBound) = expected1093 := by
    simp only [src1093, expected1093, List.map_cons, List.map_nil, bound37, bound49, bound132, bound150, bound240, bound245, bound261, bound371, bound433, bound799, bound830, bound832, bound839, bound843, bound1115, bound1140, bound1162]
  exact source1093.trans hb.symm
theorem length1093 : path1093.alternatives = (lowerHistorySourcePremises path1093).length := by
  rw [sourceIDs1093]
  rfl
theorem binding1093 : lowerHistoryPathBinding path1093 := by
  apply BindingIds19.pathBinding_from_ids path1093 src1093 [] recs1093 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1093 rfl records1093 rfl
  · intro r hr _
    simp only [recs1093, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise818)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise817)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise819)
  · intro r hr _
    simp only [recs1093, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa only [blockWids, path1093] using witness421_projection
    · simpa only [blockWids, path1093] using witness421_projection
    · simpa only [blockWids, path1093] using witness421_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1093 recs1093 records1093 length1093 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def path1094 : LowerHistoryPath := ⟨.initial,8,[2],([1],[]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([2,1,3,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,6⟩
noncomputable def raw1094 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv88]]
noncomputable def expected1094 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv88],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv88]]
theorem structural1094 (ops : RootOps19.SourceOps) (b37 b49 b88 b132 b148 b150 b240 b245 b261 b347 b371 b433 b446 b526 b571 b799 b830 b832 b839 b843 b982 b1115 b1140 b1162 : CertBound)
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
    (h180 : ops.normalization ([1,3,1],[1]) false false = b830)
    (h181 : ops.necessary ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,3,1],[1]) = some [b49])
    (h184 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,3,1],[1]) false = b982)
    (h182 : ops.pull (lowerHistoryH7) ([1,3,1],[1]) false = b150)
    (h185 : ops.pull (lowerHistoryH9) ([1,3,1],[1]) false = b446)
    (h186 : ops.normalization ([1,3,1,2],[1]) true true = b347)
    (h187 : ops.necessary ⟨⟨([2,1,3,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,3,1,2],[1]) = some [b526])
    (h188 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,3,1,2],[1]) true = b148)
    (h189 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,3,1,2],[1]) true = b571)
    (h190 : ops.pull (lowerHistoryHN) ([1,3,1,2],[1]) true = b88)
    : RootOps19.eval ops path1094 = ([[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b830,b49,b982,b347,b526,b148,b571,b88],[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b830,b49,b150,b446,b347,b526,b148,b571,b88],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b830,b49,b982,b347,b526,b148,b571,b88],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b830,b49,b150,b446,b347,b526,b148,b571,b88],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b830,b49,b982,b347,b526,b148,b571,b88],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b830,b49,b150,b446,b347,b526,b148,b571,b88]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1094, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h159, h160, h180, h181, h184, h182, h185, h186, h187, h188, h189, h190, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1094 : lowerHistorySourcePremises path1094 = raw1094.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1094 RootOps19.actualOps bv37 bv49 bv88 bv132 bv148 bv150 bv240 bv245 bv261 bv347 bv371 bv433 bv446 bv526 bv571 bv799 bv830 bv832 bv839 bv843 bv982 bv1115 bv1140 bv1162 op138 op139 op140 op141 op142 op143 op144 op145 op146 op147 op159 op160 op180 op181 op184 op182 op185 op186 op187 op188 op189 op190
theorem dedup1094 : raw1094.map List.eraseDups = expected1094 := by
  decide +kernel
theorem source1094 : lowerHistorySourcePremises path1094 = expected1094 := (rawSource1094).trans (dedup1094)
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def src1094 : List (List Nat) := [[371,843,433,1162,839,132,799,1140,245,832,37,830,49,982,347,526,148,571,88],[371,843,433,1162,839,132,799,1140,245,832,37,830,49,150,446,347,526,148,571,88],[371,843,433,1162,839,132,799,1140,1115,240,832,37,830,49,982,347,526,148,571,88],[371,843,433,1162,839,132,799,1140,1115,240,832,37,830,49,150,446,347,526,148,571,88],[371,843,433,1162,839,132,799,261,832,37,830,49,982,347,526,148,571,88],[371,843,433,1162,839,132,799,261,832,37,830,49,150,446,347,526,148,571,88]]
theorem sourceIDs1094 : lowerHistorySourcePremises path1094 = src1094.map (List.map lowerHistoryBound) := by
  have hb : src1094.map (List.map lowerHistoryBound) = expected1094 := by
    simp only [src1094, expected1094, List.map_cons, List.map_nil, bound37, bound49, bound88, bound132, bound148, bound150, bound240, bound245, bound261, bound347, bound371, bound433, bound446, bound526, bound571, bound799, bound830, bound832, bound839, bound843, bound982, bound1115, bound1140, bound1162]
  exact source1094.trans hb.symm
theorem length1094 : path1094.alternatives = (lowerHistorySourcePremises path1094).length := by
  rw [sourceIDs1094]
  rfl
theorem binding1094 : lowerHistoryPathBinding path1094 := by
  apply BindingIds19.pathBinding_from_ids path1094 src1094 [] recs1094 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1094 rfl records1094 rfl
  · intro r hr _
    simp only [recs1094, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise802)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise798)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise801)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise797)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise803)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise799)
  · intro r hr _
    simp only [recs1094, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1094] using witness369_projection
    · simpa only [blockWids, path1094] using witness369_projection
    · simpa only [blockWids, path1094] using witness369_projection
    · simpa only [blockWids, path1094] using witness369_projection
    · simpa only [blockWids, path1094] using witness369_projection
    · simpa only [blockWids, path1094] using witness369_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1094 recs1094 records1094 length1094 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
open BindingNumeric20
theorem op192 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,3,1,2],[1]) true = bv148 := by
  norm_num [bv148, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op193 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,3,1,2],[1]) true = bv571 := by
  norm_num [bv571, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op194 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,3,1,2],[1]) true = bv506 := by
  norm_num [bv506, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op195 : lowerHistoryPull (lowerHistoryH23) ([1,3,1,2],[1]) true = bv991 := by
  norm_num [bv991, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op196 : lowerHistoryNormalization ([1,3,1,2,1],[1]) true true = bv342 := by
  norm_num [bv342, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op197 : lowerHistoryNecessary ⟨⟨([2,1,3,1,2,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,3,1,2,1],[1]) = some [bv502] := by
  decide +kernel
theorem op198 : lowerHistoryPull (lowerHistoryH7) ([1,3,1,2,1],[1]) true = bv592 := by
  norm_num [bv592, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op199 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,3,1,2,1],[1]) true = bv931 := by
  norm_num [bv931, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op200 : lowerHistoryPull (lowerHistoryHN) ([1,3,1,2,1],[1]) true = bv83 := by
  norm_num [bv83, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def path1095 : LowerHistoryPath := ⟨.initial,9,[2],([1],[]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,1,3,1,2,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,12⟩
noncomputable def raw1095 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83]]
noncomputable def expected1095 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv245,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv1140,bv1115,bv240,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv982,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv978,bv342,bv502,bv592,bv931,bv83],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv832,bv37,bv830,bv49,bv150,bv446,bv347,bv526,bv148,bv571,bv506,bv991,bv342,bv502,bv592,bv931,bv83]]
theorem structural1095 (ops : RootOps19.SourceOps) (b37 b49 b83 b132 b148 b150 b240 b245 b261 b342 b347 b371 b433 b446 b502 b506 b526 b571 b592 b799 b830 b832 b839 b843 b931 b978 b982 b991 b1115 b1140 b1162 : CertBound)
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
    (h180 : ops.normalization ([1,3,1],[1]) false false = b830)
    (h181 : ops.necessary ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,3,1],[1]) = some [b49])
    (h184 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,3,1],[1]) false = b982)
    (h182 : ops.pull (lowerHistoryH7) ([1,3,1],[1]) false = b150)
    (h185 : ops.pull (lowerHistoryH9) ([1,3,1],[1]) false = b446)
    (h186 : ops.normalization ([1,3,1,2],[1]) true true = b347)
    (h187 : ops.necessary ⟨⟨([2,1,3,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,3,1,2],[1]) = some [b526])
    (h191 : ops.pull (lowerHistoryH2) ([1,3,1,2],[1]) true = b978)
    (h192 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,3,1,2],[1]) true = b148)
    (h193 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,3,1,2],[1]) true = b571)
    (h194 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,3,1,2],[1]) true = b506)
    (h195 : ops.pull (lowerHistoryH23) ([1,3,1,2],[1]) true = b991)
    (h196 : ops.normalization ([1,3,1,2,1],[1]) true true = b342)
    (h197 : ops.necessary ⟨⟨([2,1,3,1,2,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,3,1,2,1],[1]) = some [b502])
    (h198 : ops.pull (lowerHistoryH7) ([1,3,1,2,1],[1]) true = b592)
    (h199 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,3,1,2,1],[1]) true = b931)
    (h200 : ops.pull (lowerHistoryHN) ([1,3,1,2,1],[1]) true = b83)
    : RootOps19.eval ops path1095 = ([[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b830,b49,b982,b347,b526,b978,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b830,b49,b982,b347,b526,b148,b571,b506,b991,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b830,b49,b150,b446,b347,b526,b978,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b1140,b245,b832,b37,b830,b49,b150,b446,b347,b526,b148,b571,b506,b991,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b830,b49,b982,b347,b526,b978,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b830,b49,b982,b347,b526,b148,b571,b506,b991,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b830,b49,b150,b446,b347,b526,b978,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b1140,b1115,b240,b832,b37,b830,b49,b150,b446,b347,b526,b148,b571,b506,b991,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b830,b49,b982,b347,b526,b978,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b830,b49,b982,b347,b526,b148,b571,b506,b991,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b830,b49,b150,b446,b347,b526,b978,b342,b502,b592,b931,b83],[b371,b843,b433,b1162,b839,b132,b799,b261,b832,b37,b830,b49,b150,b446,b347,b526,b148,b571,b506,b991,b342,b502,b592,b931,b83]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([3],[1]) = [[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,(lowerHistoryComplement lowerHistoryH6)],[(lowerHistoryComplement lowerHistoryH2),lowerHistoryH5,lowerHistoryH6,(lowerHistoryComplement lowerHistoryH7Mixed)],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,3],[3,1,3,1]),(false,true)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,3,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,1,3,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1095, h138, h139, h140, h141, h142, h143, h144, h145, h146, h147, h159, h160, h180, h181, h184, h182, h185, h186, h187, h191, h192, h193, h194, h195, h196, h197, h198, h199, h200, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1095 : lowerHistorySourcePremises path1095 = raw1095.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1095 RootOps19.actualOps bv37 bv49 bv83 bv132 bv148 bv150 bv240 bv245 bv261 bv342 bv347 bv371 bv433 bv446 bv502 bv506 bv526 bv571 bv592 bv799 bv830 bv832 bv839 bv843 bv931 bv978 bv982 bv991 bv1115 bv1140 bv1162 op138 op139 op140 op141 op142 op143 op144 op145 op146 op147 op159 op160 op180 op181 op184 op182 op185 op186 op187 op191 op192 op193 op194 op195 op196 op197 op198 op199 op200
theorem dedup1095 : raw1095.map List.eraseDups = expected1095 := by
  decide +kernel
theorem source1095 : lowerHistorySourcePremises path1095 = expected1095 := (rawSource1095).trans (dedup1095)
end M7ContinueSep17.Initial20260918.B1090_1095

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1090_1095
noncomputable def src1095 : List (List Nat) := [[371,843,433,1162,839,132,799,1140,245,832,37,830,49,982,347,526,978,342,502,592,931,83],[371,843,433,1162,839,132,799,1140,245,832,37,830,49,982,347,526,148,571,506,991,342,502,592,931,83],[371,843,433,1162,839,132,799,1140,245,832,37,830,49,150,446,347,526,978,342,502,592,931,83],[371,843,433,1162,839,132,799,1140,245,832,37,830,49,150,446,347,526,148,571,506,991,342,502,592,931,83],[371,843,433,1162,839,132,799,1140,1115,240,832,37,830,49,982,347,526,978,342,502,592,931,83],[371,843,433,1162,839,132,799,1140,1115,240,832,37,830,49,982,347,526,148,571,506,991,342,502,592,931,83],[371,843,433,1162,839,132,799,1140,1115,240,832,37,830,49,150,446,347,526,978,342,502,592,931,83],[371,843,433,1162,839,132,799,1140,1115,240,832,37,830,49,150,446,347,526,148,571,506,991,342,502,592,931,83],[371,843,433,1162,839,132,799,261,832,37,830,49,982,347,526,978,342,502,592,931,83],[371,843,433,1162,839,132,799,261,832,37,830,49,982,347,526,148,571,506,991,342,502,592,931,83],[371,843,433,1162,839,132,799,261,832,37,830,49,150,446,347,526,978,342,502,592,931,83],[371,843,433,1162,839,132,799,261,832,37,830,49,150,446,347,526,148,571,506,991,342,502,592,931,83]]
theorem sourceIDs1095 : lowerHistorySourcePremises path1095 = src1095.map (List.map lowerHistoryBound) := by
  have hb : src1095.map (List.map lowerHistoryBound) = expected1095 := by
    simp only [src1095, expected1095, List.map_cons, List.map_nil, bound37, bound49, bound83, bound132, bound148, bound150, bound240, bound245, bound261, bound342, bound347, bound371, bound433, bound446, bound502, bound506, bound526, bound571, bound592, bound799, bound830, bound832, bound839, bound843, bound931, bound978, bound982, bound991, bound1115, bound1140, bound1162]
  exact source1095.trans hb.symm
theorem length1095 : path1095.alternatives = (lowerHistorySourcePremises path1095).length := by
  rw [sourceIDs1095]
  rfl
theorem binding1095 : lowerHistoryPathBinding path1095 := by
  apply BindingIds19.pathBinding_from_ids path1095 src1095 [] recs1095 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1095 rfl records1095 rfl
  · intro r hr _
    simp only [recs1095, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise794)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise786)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise790)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise782)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise793)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise785)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise789)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise781)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise795)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise787)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise791)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise783)
  · intro r hr _
    simp only [recs1095, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
    · simpa only [blockWids, path1095] using witness454_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1095 recs1095 records1095 length1095 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1090_1095

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
namespace M7ContinueSep17.Initial20260918.B1090_1095
theorem _root_.solution : lowerHistoryBindingBatch 1090 1095 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1090]? = some M7ContinueSep17.Initial20260918.B1090_1095.path1091 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 4 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1091
  · have hl : lowerHistoryPaths[1091]? = some M7ContinueSep17.Initial20260918.B1090_1095.path1092 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 5 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1092
  · have hl : lowerHistoryPaths[1092]? = some M7ContinueSep17.Initial20260918.B1090_1095.path1093 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 6 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1093
  · have hl : lowerHistoryPaths[1093]? = some M7ContinueSep17.Initial20260918.B1090_1095.path1094 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 7 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1094
  · have hl : lowerHistoryPaths[1094]? = some M7ContinueSep17.Initial20260918.B1090_1095.path1095 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 8 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1095
end M7ContinueSep17.Initial20260918.B1090_1095

#print axioms solution
