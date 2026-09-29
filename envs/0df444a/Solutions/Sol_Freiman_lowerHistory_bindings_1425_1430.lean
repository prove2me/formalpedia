-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1425_1430
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T07:26:34.337464+00:00
-- url     : https://prove2.me/submissions/59b571e4-c946-4c21-9bd6-0c2d8a16d43a

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
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def bv18 : CertBound := ⟨true,false,⟨⟨(-1/5),(0),(0),(2/35)⟩,⟨(1/2),(0),(0),(1/42)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv48 : CertBound := ⟨true,false,⟨⟨(-336539/6776858),(256167/6776858),(0),(0)⟩,⟨(277/454),(1/454),(0),(0)⟩,⟨(402/649),(-1/649),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv63 : CertBound := ⟨true,false,⟨⟨(-38189/2003254),(29057/2003254),(0),(0)⟩,⟨(1051/1702),(1/1702),(0),(0)⟩,⟨(731/1177),(-1/1177),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv68 : CertBound := ⟨true,false,⟨⟨(-2869/205531),(0),(0),(664/205531)⟩,⟨(5429/8746),(0),(0),(1/8746)⟩,⟨(63/94),(0),(0),(-1/94)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv69 : CertBound := ⟨true,false,⟨⟨(-2257/165722),(0),(0),(567/165722)⟩,⟨(2185/3526),(0),(0),(1/3526)⟩,⟨(63/94),(0),(0),(-1/94)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv103 : CertBound := ⟨true,false,⟨⟨(-439/196265),(0),(0),(472/588795)⟩,⟨(2859/4618),(0),(0),(1/4618)⟩,⟨(107/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv106 : CertBound := ⟨true,false,⟨⟨(-47/25670),(0),(0),(91/77010)⟩,⟨(931/1510),(0),(0),(1/1510)⟩,⟨(107/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv124 : CertBound := ⟨true,false,⟨⟨(1525035150/600679919281),(52292950/1802039757843),(0),(0)⟩,⟨(50251/80882),(-1/242646),(0),(0)⟩,⟨(54614/87889),(1/87889),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv125 : CertBound := ⟨true,false,⟨⟨(157/56212),(1831/84318),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv129 : CertBound := ⟨true,false,⟨⟨(99302484850/22945528938527),(1075412750/22945528938527),(0),(0)⟩,⟨(87467/141046),(-1/141046),(0),(0)⟩,⟨(32277/52033),(1/52033),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv131 : CertBound := ⟨true,false,⟨⟨(6862253/1285574550),(184543/128557455),(0),(0)⟩,⟨(51/83),(1/249),(0),(0)⟩,⟨(380/611),(-1/1833),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv132 : CertBound := ⟨true,false,⟨⟨(133/21164),(324/5291),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv221 : CertBound := ⟨true,false,⟨⟨(7202600/98290907),(-28450/98290907),(0),(0)⟩,⟨(876/1429),(-1/1429),(0),(0)⟩,⟨(2305/3718),(1/3718),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv316 : CertBound := ⟨true,true,⟨⟨(-5/94),(0),(0),(11/658)⟩,⟨(1/2),(0),(0),(1/42)⟩,⟨(63/94),(0),(0),(-1/94)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv330 : CertBound := ⟨true,true,⟨⟨(-2869/205531),(0),(0),(664/205531)⟩,⟨(5429/8746),(0),(0),(1/8746)⟩,⟨(63/94),(0),(0),(-1/94)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv331 : CertBound := ⟨true,true,⟨⟨(-2257/165722),(0),(0),(567/165722)⟩,⟨(2185/3526),(0),(0),(1/3526)⟩,⟨(63/94),(0),(0),(-1/94)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv359 : CertBound := ⟨true,true,⟨⟨(-439/196265),(0),(0),(472/588795)⟩,⟨(2859/4618),(0),(0),(1/4618)⟩,⟨(107/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv361 : CertBound := ⟨true,true,⟨⟨(-47/25670),(0),(0),(91/77010)⟩,⟨(931/1510),(0),(0),(1/1510)⟩,⟨(107/170),(0),(0),(-1/510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv433 : CertBound := ⟨true,true,⟨⟨(729/1024),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv447 : CertBound := ⟨false,false,⟨⟨(-3/10),(0),(0),(1/10)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv460 : CertBound := ⟨false,false,⟨⟨(-1/47),(0),(0),(16/987)⟩,⟨(1/2),(0),(0),(1/42)⟩,⟨(63/94),(0),(0),(-1/94)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv461 : CertBound := ⟨false,false,⟨⟨(-121/12314),(0),(0),(81/12314)⟩,⟨(157/262),(0),(0),(1/262)⟩,⟨(63/94),(0),(0),(-1/94)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv477 : CertBound := ⟨false,false,⟨⟨(22256969/17701635601),(16601031/17701635601),(0),(0)⟩,⟨(9627/15493),(-1/15493),(0),(0)⟩,⟨(54614/87889),(1/87889),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv482 : CertBound := ⟨false,false,⟨⟨(10198/6694259),(55105/20082777),(0),(0)⟩,⟨(2305/3718),(1/3718),(0),(0)⟩,⟨(1890/3047),(-1/9141),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv483 : CertBound := ⟨false,false,⟨⟨(1137028/698102327),(7935808/2094306981),(0),(0)⟩,⟨(54614/87889),(1/87889),(0),(0)⟩,⟨(380/611),(-1/1833),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv484 : CertBound := ⟨false,false,⟨⟨(215989/129576722),(221999/129576722),(0),(0)⟩,⟨(144931/233893),(1/233893),(0),(0)⟩,⟨(1890/3047),(-1/9141),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv496 : CertBound := ⟨false,false,⟨⟨(7265/2585869),(19194/2585869),(0),(0)⟩,⟨(2305/3718),(1/3718),(0),(0)⟩,⟨(731/1177),(-1/1177),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv498 : CertBound := ⟨false,false,⟨⟨(235240850000/77876223443379),(9209779000/77876223443379),(0),(0)⟩,⟨(7982/12853),(1/12853),(0),(0)⟩,⟨(50251/80882),(-1/242646),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv510 : CertBound := ⟨false,false,⟨⟨(9316650/2103929399),(-90823450/65221811369),(0),(0)⟩,⟨(26192/42157),(1/42157),(0),(0)⟩,⟨(5639/9074),(-1/27222),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv519 : CertBound := ⟨false,false,⟨⟨(133593938000/25150524470163),(13162025000/75451573410489),(0),(0)⟩,⟨(4425/7141),(1/7141),(0),(0)⟩,⟨(87467/141046),(-1/141046),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv534 : CertBound := ⟨false,false,⟨⟨(46381350/6179742833),(-14551050/6179742833),(0),(0)⟩,⟨(15219/24541),(1/24541),(0),(0)⟩,⟨(10079/16246),(-1/16246),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv610 : CertBound := ⟨false,false,⟨⟨(171/7802),(1097/23406),(0),(0)⟩,⟨(51/83),(1/249),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv669 : CertBound := ⟨false,false,⟨⟨(85219/1832972),(176329/5498916),(0),(0)⟩,⟨(51/83),(1/249),(0),(0)⟩,⟨(3530/5521),(-1/5521),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv694 : CertBound := ⟨false,false,⟨⟨(211/3478),(425/3478),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv737 : CertBound := ⟨false,false,⟨⟨(2000/16731),(-2500/518661),(0),(0)⟩,⟨(2305/3718),(1/3718),(0),(0)⟩,⟨(108/169),(-1/169),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(66/179),(-1/537),(0),(0)⟩⟩⟩
noncomputable def bv778 : CertBound := ⟨false,false,⟨⟨(88497/351923),(-48209/351923),(0),(0)⟩,⟨(731/1177),(-1/1177),(0),(0)⟩,⟨(16/23),(-1/23),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv839 : CertBound := ⟨false,false,⟨⟨(9/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv914 : CertBound := ⟨false,true,⟨⟨(315884/573798927),(205859/573798927),(0),(0)⟩,⟨(26192/42157),(1/42157),(0),(0)⟩,⟨(5639/9074),(-1/27222),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv918 : CertBound := ⟨false,true,⟨⟨(186572/199346543),(364601/598039629),(0),(0)⟩,⟨(15219/24541),(1/24541),(0),(0)⟩,⟨(10079/16246),(-1/16246),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv934 : CertBound := ⟨false,true,⟨⟨(1525035150/600679919281),(52292950/1802039757843),(0),(0)⟩,⟨(50251/80882),(-1/242646),(0),(0)⟩,⟨(54614/87889),(1/87889),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv950 : CertBound := ⟨false,true,⟨⟨(99302484850/22945528938527),(1075412750/22945528938527),(0),(0)⟩,⟨(87467/141046),(-1/141046),(0),(0)⟩,⟨(32277/52033),(1/52033),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv952 : CertBound := ⟨false,true,⟨⟨(6862253/1285574550),(184543/128557455),(0),(0)⟩,⟨(51/83),(1/249),(0),(0)⟩,⟨(380/611),(-1/1833),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv956 : CertBound := ⟨false,true,⟨⟨(19064286750/3079723119187),(-733840750/3079723119187),(0),(0)⟩,⟨(2305/3718),(1/3718),(0),(0)⟩,⟨(87467/141046),(-1/141046),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1079 : CertBound := ⟨false,true,⟨⟨(7202600/98290907),(-28450/98290907),(0),(0)⟩,⟨(876/1429),(-1/1429),(0),(0)⟩,⟨(2305/3718),(1/3718),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1102 : CertBound := ⟨false,true,⟨⟨(1337250/12144847),(-108500/12144847),(0),(0)⟩,⟨(2305/3718),(1/3718),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1162 : CertBound := ⟨false,true,⟨⟨(225/289),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
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
theorem op140 : lowerHistoryNormalization ([1,1,1],[]) true false = bv18 := by
  norm_num [bv18, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op141 : lowerHistoryNecessary ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([1,1,1],[]) = some [bv694] := by
  decide +kernel
theorem op142 : lowerHistoryPull (lowerHistoryH2) ([1,1,1],[]) true = bv1079 := by
  norm_num [bv1079, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op143 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,1],[]) true = bv221 := by
  norm_num [bv221, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op144 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,1],[]) true = bv737 := by
  norm_num [bv737, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op145 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,1],[]) true = bv669 := by
  norm_num [bv669, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
open BindingNumeric20
theorem op146 : lowerHistoryPull (lowerHistoryH23) ([1,1,1],[]) true = bv1102 := by
  norm_num [bv1102, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op147 : lowerHistoryNormalization ([1,1,1,1],[]) true true = bv316 := by
  norm_num [bv316, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op148 : lowerHistoryNecessary ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,1,1],[]) = some [bv610] := by
  decide +kernel
theorem op149 : lowerHistoryNormalization ([1,1,1,1],[1]) false false = bv460 := by
  norm_num [bv460, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op150 : lowerHistoryNecessary ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,1,1],[1]) = some [bv48] := by
  decide +kernel
theorem op173 : lowerHistoryNormalization ([1,1,1,1,1],[1]) false false = bv461 := by
  norm_num [bv461, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op174 : lowerHistoryNecessary ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,1,1,1],[1]) = some [bv63] := by
  decide +kernel
theorem op175 : lowerHistoryPull (lowerHistoryH7) ([1,1,1,1,1],[1]) false = bv131 := by
  norm_num [bv131, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op176 : lowerHistoryPull (lowerHistoryHN) ([1,1,1,1,1],[1]) false = bv461 := by
  norm_num [bv461, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op177 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,1,1,1],[1]) false = bv952 := by
  norm_num [bv952, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op178 : lowerHistoryNormalization ([1,1,1,1,1,3],[1]) true true = bv331 := by
  norm_num [bv331, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op179 : lowerHistoryNecessary ⟨⟨([3,1,1,1,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,1,1,1,3],[1]) = some [bv483] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def path1426 : LowerHistoryPath := ⟨.initial,340,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,1,1,1,1,1],[3,1,3,1]),(true,true),false,2,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩
noncomputable def raw1426 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv461],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv461]]
noncomputable def expected1426 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv131],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv131]]
theorem structural1426 (ops : RootOps19.SourceOps) (b18 b48 b63 b125 b131 b132 b221 b316 b371 b433 b447 b460 b461 b610 b669 b694 b737 b839 b843 b1079 b1102 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h140 : ops.normalization ([1,1,1],[]) true false = b18)
    (h141 : ops.necessary ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([1,1,1],[]) = some [b694])
    (h142 : ops.pull (lowerHistoryH2) ([1,1,1],[]) true = b1079)
    (h143 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,1],[]) true = b221)
    (h144 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,1],[]) true = b737)
    (h145 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,1],[]) true = b669)
    (h146 : ops.pull (lowerHistoryH23) ([1,1,1],[]) true = b1102)
    (h147 : ops.normalization ([1,1,1,1],[]) true true = b316)
    (h148 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,1,1],[]) = some [b610])
    (h149 : ops.normalization ([1,1,1,1],[1]) false false = b460)
    (h150 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,1,1],[1]) = some [b48])
    (h173 : ops.normalization ([1,1,1,1,1],[1]) false false = b461)
    (h174 : ops.necessary ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,1,1,1],[1]) = some [b63])
    (h175 : ops.pull (lowerHistoryH7) ([1,1,1,1,1],[1]) false = b131)
    (h176 : ops.pull (lowerHistoryHN) ([1,1,1,1,1],[1]) false = b461)
    : RootOps19.eval ops path1426 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b1079,b316,b610,b460,b48,b461,b63,b131,b461],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b221,b737,b669,b1102,b316,b610,b460,b48,b461,b63,b131,b461]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1426, h0, h1, h2, h3, h4, h5, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h173, h174, h175, h176, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1426 : lowerHistorySourcePremises path1426 = raw1426.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1426 RootOps19.actualOps bv18 bv48 bv63 bv125 bv131 bv132 bv221 bv316 bv371 bv433 bv447 bv460 bv461 bv610 bv669 bv694 bv737 bv839 bv843 bv1079 bv1102 bv1162 op0 op1 op2 op3 op4 op5 op140 op141 op142 op143 op144 op145 op146 op147 op148 op149 op150 op173 op174 op175 op176
theorem dedup1426 : raw1426.map List.eraseDups = expected1426 := by
  decide +kernel
theorem source1426 : lowerHistorySourcePremises path1426 = expected1426 := (rawSource1426).trans (dedup1426)
end M7ContinueSep17.Initial20260918.B1425_1430

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
namespace M7ContinueSep17.Initial20260918.B1425_1430
theorem bound18 : lowerHistoryBound 18 = bv18 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[17]? = some bv18 := Eq.refl (some bv18)
  exact (BoundCompact16.global_to_chunk1 17 (by decide)).trans hl
theorem bound48 : lowerHistoryBound 48 = bv48 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[47]? = some bv48 := Eq.refl (some bv48)
  exact (BoundCompact16.global_to_chunk1 47 (by decide)).trans hl
theorem bound63 : lowerHistoryBound 63 = bv63 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[62]? = some bv63 := Eq.refl (some bv63)
  exact (BoundCompact16.global_to_chunk1 62 (by decide)).trans hl
theorem bound68 : lowerHistoryBound 68 = bv68 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[67]? = some bv68 := Eq.refl (some bv68)
  exact (BoundCompact16.global_to_chunk1 67 (by decide)).trans hl
theorem bound69 : lowerHistoryBound 69 = bv69 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[68]? = some bv69 := Eq.refl (some bv69)
  exact (BoundCompact16.global_to_chunk1 68 (by decide)).trans hl
theorem bound103 : lowerHistoryBound 103 = bv103 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[102]? = some bv103 := Eq.refl (some bv103)
  exact (BoundCompact16.global_to_chunk1 102 (by decide)).trans hl
theorem bound106 : lowerHistoryBound 106 = bv106 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[105]? = some bv106 := Eq.refl (some bv106)
  exact (BoundCompact16.global_to_chunk1 105 (by decide)).trans hl
theorem bound124 : lowerHistoryBound 124 = bv124 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[123]? = some bv124 := Eq.refl (some bv124)
  exact (BoundCompact16.global_to_chunk1 123 (by decide)).trans hl
theorem bound125 : lowerHistoryBound 125 = bv125 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[124]? = some bv125 := Eq.refl (some bv125)
  exact (BoundCompact16.global_to_chunk1 124 (by decide)).trans hl
theorem bound129 : lowerHistoryBound 129 = bv129 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[128]? = some bv129 := Eq.refl (some bv129)
  exact (BoundCompact16.global_to_chunk1 128 (by decide)).trans hl
theorem bound131 : lowerHistoryBound 131 = bv131 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[130]? = some bv131 := Eq.refl (some bv131)
  exact (BoundCompact16.global_to_chunk1 130 (by decide)).trans hl
theorem bound132 : lowerHistoryBound 132 = bv132 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[131]? = some bv132 := Eq.refl (some bv132)
  exact (BoundCompact16.global_to_chunk1 131 (by decide)).trans hl
theorem bound221 : lowerHistoryBound 221 = bv221 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[20]? = some bv221 := Eq.refl (some bv221)
  exact (BoundCompact16.global_to_chunk2 20 (by decide)).trans hl
theorem bound316 : lowerHistoryBound 316 = bv316 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[115]? = some bv316 := Eq.refl (some bv316)
  exact (BoundCompact16.global_to_chunk2 115 (by decide)).trans hl
theorem bound330 : lowerHistoryBound 330 = bv330 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[129]? = some bv330 := Eq.refl (some bv330)
  exact (BoundCompact16.global_to_chunk2 129 (by decide)).trans hl
theorem bound331 : lowerHistoryBound 331 = bv331 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[130]? = some bv331 := Eq.refl (some bv331)
  exact (BoundCompact16.global_to_chunk2 130 (by decide)).trans hl
theorem bound359 : lowerHistoryBound 359 = bv359 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[158]? = some bv359 := Eq.refl (some bv359)
  exact (BoundCompact16.global_to_chunk2 158 (by decide)).trans hl
theorem bound361 : lowerHistoryBound 361 = bv361 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[160]? = some bv361 := Eq.refl (some bv361)
  exact (BoundCompact16.global_to_chunk2 160 (by decide)).trans hl
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
theorem bound460 : lowerHistoryBound 460 = bv460 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[59]? = some bv460 := Eq.refl (some bv460)
  exact (BoundCompact16.global_to_chunk3 59 (by decide)).trans hl
theorem bound461 : lowerHistoryBound 461 = bv461 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[60]? = some bv461 := Eq.refl (some bv461)
  exact (BoundCompact16.global_to_chunk3 60 (by decide)).trans hl
theorem bound477 : lowerHistoryBound 477 = bv477 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[76]? = some bv477 := Eq.refl (some bv477)
  exact (BoundCompact16.global_to_chunk3 76 (by decide)).trans hl
theorem bound482 : lowerHistoryBound 482 = bv482 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[81]? = some bv482 := Eq.refl (some bv482)
  exact (BoundCompact16.global_to_chunk3 81 (by decide)).trans hl
theorem bound483 : lowerHistoryBound 483 = bv483 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[82]? = some bv483 := Eq.refl (some bv483)
  exact (BoundCompact16.global_to_chunk3 82 (by decide)).trans hl
theorem bound484 : lowerHistoryBound 484 = bv484 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[83]? = some bv484 := Eq.refl (some bv484)
  exact (BoundCompact16.global_to_chunk3 83 (by decide)).trans hl
theorem bound496 : lowerHistoryBound 496 = bv496 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[95]? = some bv496 := Eq.refl (some bv496)
  exact (BoundCompact16.global_to_chunk3 95 (by decide)).trans hl
theorem bound498 : lowerHistoryBound 498 = bv498 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[97]? = some bv498 := Eq.refl (some bv498)
  exact (BoundCompact16.global_to_chunk3 97 (by decide)).trans hl
theorem bound510 : lowerHistoryBound 510 = bv510 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[109]? = some bv510 := Eq.refl (some bv510)
  exact (BoundCompact16.global_to_chunk3 109 (by decide)).trans hl
theorem bound519 : lowerHistoryBound 519 = bv519 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[118]? = some bv519 := Eq.refl (some bv519)
  exact (BoundCompact16.global_to_chunk3 118 (by decide)).trans hl
theorem bound534 : lowerHistoryBound 534 = bv534 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[133]? = some bv534 := Eq.refl (some bv534)
  exact (BoundCompact16.global_to_chunk3 133 (by decide)).trans hl
theorem bound610 : lowerHistoryBound 610 = bv610 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[9]? = some bv610 := Eq.refl (some bv610)
  exact (BoundCompact16.global_to_chunk4 9 (by decide)).trans hl
theorem bound669 : lowerHistoryBound 669 = bv669 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[68]? = some bv669 := Eq.refl (some bv669)
  exact (BoundCompact16.global_to_chunk4 68 (by decide)).trans hl
theorem bound694 : lowerHistoryBound 694 = bv694 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[93]? = some bv694 := Eq.refl (some bv694)
  exact (BoundCompact16.global_to_chunk4 93 (by decide)).trans hl
theorem bound737 : lowerHistoryBound 737 = bv737 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[136]? = some bv737 := Eq.refl (some bv737)
  exact (BoundCompact16.global_to_chunk4 136 (by decide)).trans hl
theorem bound778 : lowerHistoryBound 778 = bv778 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[177]? = some bv778 := Eq.refl (some bv778)
  exact (BoundCompact16.global_to_chunk4 177 (by decide)).trans hl
theorem bound839 : lowerHistoryBound 839 = bv839 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[38]? = some bv839 := Eq.refl (some bv839)
  exact (BoundCompact16.global_to_chunk5 38 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound914 : lowerHistoryBound 914 = bv914 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[113]? = some bv914 := Eq.refl (some bv914)
  exact (BoundCompact16.global_to_chunk5 113 (by decide)).trans hl
theorem bound918 : lowerHistoryBound 918 = bv918 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[117]? = some bv918 := Eq.refl (some bv918)
  exact (BoundCompact16.global_to_chunk5 117 (by decide)).trans hl
theorem bound934 : lowerHistoryBound 934 = bv934 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[133]? = some bv934 := Eq.refl (some bv934)
  exact (BoundCompact16.global_to_chunk5 133 (by decide)).trans hl
theorem bound950 : lowerHistoryBound 950 = bv950 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[149]? = some bv950 := Eq.refl (some bv950)
  exact (BoundCompact16.global_to_chunk5 149 (by decide)).trans hl
theorem bound952 : lowerHistoryBound 952 = bv952 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[151]? = some bv952 := Eq.refl (some bv952)
  exact (BoundCompact16.global_to_chunk5 151 (by decide)).trans hl
theorem bound956 : lowerHistoryBound 956 = bv956 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[155]? = some bv956 := Eq.refl (some bv956)
  exact (BoundCompact16.global_to_chunk5 155 (by decide)).trans hl
theorem bound1079 : lowerHistoryBound 1079 = bv1079 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[78]? = some bv1079 := Eq.refl (some bv1079)
  exact (BoundCompact16.global_to_chunk6 78).trans hl
theorem bound1102 : lowerHistoryBound 1102 = bv1102 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[101]? = some bv1102 := Eq.refl (some bv1102)
  exact (BoundCompact16.global_to_chunk6 101).trans hl
theorem bound1162 : lowerHistoryBound 1162 = bv1162 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[161]? = some bv1162 := Eq.refl (some bv1162)
  exact (BoundCompact16.global_to_chunk6 161).trans hl
end M7ContinueSep17.Initial20260918.B1425_1430

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
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def recs1426 : List LowerHistoryRecord := [⟨.initial,340,0,(-1),false,716,337⟩,⟨.initial,340,1,(-1),false,715,337⟩]
theorem records1426 : lowerHistoryRecordsFor (⟨.initial,340,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,1,1,1,1,1],[3,1,3,1]),(true,true),false,2,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1426 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 340)) = recs1426
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1427 : List LowerHistoryRecord := [⟨.initial,341,0,(-1),false,696,351⟩,⟨.initial,341,1,(-1),false,695,351⟩]
theorem records1427 : lowerHistoryRecordsFor (⟨.initial,341,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,1,1,1,1,3],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1427 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 341)) = recs1427
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1428 : List LowerHistoryRecord := [⟨.initial,342,0,(-1),false,694,434⟩,⟨.initial,342,1,(-1),false,693,434⟩]
theorem records1428 : lowerHistoryRecordsFor (⟨.initial,342,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,1,1,1,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1428 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 342)) = recs1428
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1429 : List LowerHistoryRecord := [⟨.initial,343,0,(-1),false,714,357⟩,⟨.initial,343,1,(-1),false,712,357⟩,⟨.initial,343,2,(-1),false,713,357⟩,⟨.initial,343,3,(-1),false,711,357⟩]
theorem records1429 : lowerHistoryRecordsFor (⟨.initial,343,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,1,1,1,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,4⟩ : LowerHistoryPath) = recs1429 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 343)) = recs1429
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1430 : List LowerHistoryRecord := [⟨.initial,344,0,(-1),false,710,440⟩,⟨.initial,344,1,(-1),false,706,440⟩,⟨.initial,344,2,(-1),false,708,440⟩,⟨.initial,344,3,(-1),false,704,440⟩,⟨.initial,344,4,(-1),false,709,440⟩,⟨.initial,344,5,(-1),false,705,440⟩,⟨.initial,344,6,(-1),false,707,440⟩,⟨.initial,344,7,(-1),false,703,440⟩]
theorem records1430 : lowerHistoryRecordsFor (⟨.initial,344,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,1,1,1,1,2,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,8⟩ : LowerHistoryPath) = recs1430 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 344)) = recs1430
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
end M7ContinueSep17.Initial20260918.B1425_1430

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
namespace M7ContinueSep17.Initial20260918.B1425_1430
theorem premise693 : lowerHistoryPremises[692]? = some ([18,48,63,68,125,132,221,316,330,331,371,433,447,460,461,477,483,510,610,669,694,737,839,843,914,934,952,1102,1162] : List Nat) := by
  have hg : lowerHistoryPremises[692]? = lowerHistoryPremises04[92]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 92 (by decide)
  exact hg.trans (by rfl)
theorem premise694 : lowerHistoryPremises[693]? = some ([18,48,63,68,125,132,316,330,331,371,433,447,460,461,477,483,510,610,694,839,843,914,934,952,1079,1162] : List Nat) := by
  have hg : lowerHistoryPremises[693]? = lowerHistoryPremises04[93]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 93 (by decide)
  exact hg.trans (by rfl)
theorem premise695 : lowerHistoryPremises[694]? = some ([18,48,63,69,124,125,132,221,316,331,371,433,447,460,461,483,498,610,669,694,737,839,843,952,1102,1162] : List Nat) := by
  have hg : lowerHistoryPremises[694]? = lowerHistoryPremises04[94]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 94 (by decide)
  exact hg.trans (by rfl)
theorem premise696 : lowerHistoryPremises[695]? = some ([18,48,63,69,124,125,132,316,331,371,433,447,460,461,483,498,610,694,839,843,952,1079,1162] : List Nat) := by
  have hg : lowerHistoryPremises[695]? = lowerHistoryPremises04[95]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 95 (by decide)
  exact hg.trans (by rfl)
theorem premise703 : lowerHistoryPremises[702]? = some ([18,48,63,103,125,129,131,132,221,316,359,361,371,433,447,460,461,482,484,496,519,534,610,669,694,737,778,839,843,918,956,1102,1162] : List Nat) := by
  have hg : lowerHistoryPremises[702]? = lowerHistoryPremises04[102]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 102 (by decide)
  exact hg.trans (by rfl)
theorem premise704 : lowerHistoryPremises[703]? = some ([18,48,63,103,125,129,131,132,316,359,361,371,433,447,460,461,482,484,496,519,534,610,694,778,839,843,918,956,1079,1162] : List Nat) := by
  have hg : lowerHistoryPremises[703]? = lowerHistoryPremises04[103]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 103 (by decide)
  exact hg.trans (by rfl)
theorem premise705 : lowerHistoryPremises[704]? = some ([18,48,63,103,125,129,132,221,316,359,361,371,433,447,460,461,482,484,496,519,534,610,669,694,737,839,843,918,952,956,1102,1162] : List Nat) := by
  have hg : lowerHistoryPremises[704]? = lowerHistoryPremises04[104]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 104 (by decide)
  exact hg.trans (by rfl)
theorem premise706 : lowerHistoryPremises[705]? = some ([18,48,63,103,125,129,132,316,359,361,371,433,447,460,461,482,484,496,519,534,610,694,839,843,918,952,956,1079,1162] : List Nat) := by
  have hg : lowerHistoryPremises[705]? = lowerHistoryPremises04[105]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 105 (by decide)
  exact hg.trans (by rfl)
theorem premise707 : lowerHistoryPremises[706]? = some ([18,48,63,103,125,131,132,221,316,359,361,371,433,447,460,461,482,496,534,610,669,694,737,778,839,843,918,950,1102,1162] : List Nat) := by
  have hg : lowerHistoryPremises[706]? = lowerHistoryPremises04[106]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 106 (by decide)
  exact hg.trans (by rfl)
theorem premise708 : lowerHistoryPremises[707]? = some ([18,48,63,103,125,131,132,316,359,361,371,433,447,460,461,482,496,534,610,694,778,839,843,918,950,1079,1162] : List Nat) := by
  have hg : lowerHistoryPremises[707]? = lowerHistoryPremises04[107]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 107 (by decide)
  exact hg.trans (by rfl)
theorem premise709 : lowerHistoryPremises[708]? = some ([18,48,63,103,125,132,221,316,359,361,371,433,447,460,461,482,496,534,610,669,694,737,839,843,918,950,952,1102,1162] : List Nat) := by
  have hg : lowerHistoryPremises[708]? = lowerHistoryPremises04[108]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 108 (by decide)
  exact hg.trans (by rfl)
theorem premise710 : lowerHistoryPremises[709]? = some ([18,48,63,103,125,132,316,359,361,371,433,447,460,461,482,496,534,610,694,839,843,918,950,952,1079,1162] : List Nat) := by
  have hg : lowerHistoryPremises[709]? = lowerHistoryPremises04[109]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 109 (by decide)
  exact hg.trans (by rfl)
theorem premise711 : lowerHistoryPremises[710]? = some ([18,48,63,106,125,129,131,132,221,316,361,371,433,447,460,461,496,519,610,669,694,737,778,839,843,1102,1162] : List Nat) := by
  have hg : lowerHistoryPremises[710]? = lowerHistoryPremises04[110]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 110 (by decide)
  exact hg.trans (by rfl)
theorem premise712 : lowerHistoryPremises[711]? = some ([18,48,63,106,125,129,131,132,316,361,371,433,447,460,461,496,519,610,694,778,839,843,1079,1162] : List Nat) := by
  have hg : lowerHistoryPremises[711]? = lowerHistoryPremises04[111]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 111 (by decide)
  exact hg.trans (by rfl)
theorem premise713 : lowerHistoryPremises[712]? = some ([18,48,63,106,125,129,132,221,316,361,371,433,447,460,461,496,519,610,669,694,737,839,843,952,1102,1162] : List Nat) := by
  have hg : lowerHistoryPremises[712]? = lowerHistoryPremises04[112]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 112 (by decide)
  exact hg.trans (by rfl)
theorem premise714 : lowerHistoryPremises[713]? = some ([18,48,63,106,125,129,132,316,361,371,433,447,460,461,496,519,610,694,839,843,952,1079,1162] : List Nat) := by
  have hg : lowerHistoryPremises[713]? = lowerHistoryPremises04[113]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 113 (by decide)
  exact hg.trans (by rfl)
theorem premise715 : lowerHistoryPremises[714]? = some ([18,48,63,125,131,132,221,316,371,433,447,460,461,610,669,694,737,839,843,1102,1162] : List Nat) := by
  have hg : lowerHistoryPremises[714]? = lowerHistoryPremises04[114]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 114 (by decide)
  exact hg.trans (by rfl)
theorem premise716 : lowerHistoryPremises[715]? = some ([18,48,63,125,131,132,316,371,433,447,460,461,610,694,839,843,1079,1162] : List Nat) := by
  have hg : lowerHistoryPremises[715]? = lowerHistoryPremises04[115]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 115 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1425_1430
theorem witness337_projection : (lowerHistoryWitness 337).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 337).upperBound = lowerHistoryBound 461 ∧ (lowerHistoryWitness 337).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[136]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 461, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 461, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[336]? = lowerHistoryWitnesses02[136]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 136 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness351_projection : (lowerHistoryWitness 351).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 351).upperBound = lowerHistoryBound 498 ∧ (lowerHistoryWitness 351).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[150]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 498, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 498, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[350]? = lowerHistoryWitnesses02[150]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 150 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness357_projection : (lowerHistoryWitness 357).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 357).upperBound = lowerHistoryBound 519 ∧ (lowerHistoryWitness 357).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[156]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 519, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 519, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[356]? = lowerHistoryWitnesses02[156]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 156 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness434_projection : (lowerHistoryWitness 434).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 434).upperBound = lowerHistoryBound 914 ∧ (lowerHistoryWitness 434).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[33]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 914, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 914, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[433]? = lowerHistoryWitnesses03[33]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 33 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness440_projection : (lowerHistoryWitness 440).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 440).upperBound = lowerHistoryBound 918 ∧ (lowerHistoryWitness 440).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[39]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 918, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 918, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[439]? = lowerHistoryWitnesses03[39]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 39 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 337 => (433,461)
  | 351 => (433,498)
  | 357 => (433,519)
  | 434 => (433,914)
  | 440 => (433,918)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 693 => [18,48,63,68,125,132,221,316,330,331,371,433,447,460,461,477,483,510,610,669,694,737,839,843,914,934,952,1102,1162]
  | 694 => [18,48,63,68,125,132,316,330,331,371,433,447,460,461,477,483,510,610,694,839,843,914,934,952,1079,1162]
  | 695 => [18,48,63,69,124,125,132,221,316,331,371,433,447,460,461,483,498,610,669,694,737,839,843,952,1102,1162]
  | 696 => [18,48,63,69,124,125,132,316,331,371,433,447,460,461,483,498,610,694,839,843,952,1079,1162]
  | 703 => [18,48,63,103,125,129,131,132,221,316,359,361,371,433,447,460,461,482,484,496,519,534,610,669,694,737,778,839,843,918,956,1102,1162]
  | 704 => [18,48,63,103,125,129,131,132,316,359,361,371,433,447,460,461,482,484,496,519,534,610,694,778,839,843,918,956,1079,1162]
  | 705 => [18,48,63,103,125,129,132,221,316,359,361,371,433,447,460,461,482,484,496,519,534,610,669,694,737,839,843,918,952,956,1102,1162]
  | 706 => [18,48,63,103,125,129,132,316,359,361,371,433,447,460,461,482,484,496,519,534,610,694,839,843,918,952,956,1079,1162]
  | 707 => [18,48,63,103,125,131,132,221,316,359,361,371,433,447,460,461,482,496,534,610,669,694,737,778,839,843,918,950,1102,1162]
  | 708 => [18,48,63,103,125,131,132,316,359,361,371,433,447,460,461,482,496,534,610,694,778,839,843,918,950,1079,1162]
  | 709 => [18,48,63,103,125,132,221,316,359,361,371,433,447,460,461,482,496,534,610,669,694,737,839,843,918,950,952,1102,1162]
  | 710 => [18,48,63,103,125,132,316,359,361,371,433,447,460,461,482,496,534,610,694,839,843,918,950,952,1079,1162]
  | 711 => [18,48,63,106,125,129,131,132,221,316,361,371,433,447,460,461,496,519,610,669,694,737,778,839,843,1102,1162]
  | 712 => [18,48,63,106,125,129,131,132,316,361,371,433,447,460,461,496,519,610,694,778,839,843,1079,1162]
  | 713 => [18,48,63,106,125,129,132,221,316,361,371,433,447,460,461,496,519,610,669,694,737,839,843,952,1102,1162]
  | 714 => [18,48,63,106,125,129,132,316,361,371,433,447,460,461,496,519,610,694,839,843,952,1079,1162]
  | 715 => [18,48,63,125,131,132,221,316,371,433,447,460,461,610,669,694,737,839,843,1102,1162]
  | 716 => [18,48,63,125,131,132,316,371,433,447,460,461,610,694,839,843,1079,1162]
  | _ => []
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def src1426 : List (List Nat) := [[371,843,433,1162,839,132,447,125,18,694,1079,316,610,460,48,461,63,131],[371,843,433,1162,839,132,447,125,18,694,221,737,669,1102,316,610,460,48,461,63,131]]
theorem sourceIDs1426 : lowerHistorySourcePremises path1426 = src1426.map (List.map lowerHistoryBound) := by
  have hb : src1426.map (List.map lowerHistoryBound) = expected1426 := by
    simp only [src1426, expected1426, List.map_cons, List.map_nil, bound18, bound48, bound63, bound125, bound131, bound132, bound221, bound316, bound371, bound433, bound447, bound460, bound461, bound610, bound669, bound694, bound737, bound839, bound843, bound1079, bound1102, bound1162]
  exact source1426.trans hb.symm
theorem length1426 : path1426.alternatives = (lowerHistorySourcePremises path1426).length := by
  rw [sourceIDs1426]
  rfl
theorem binding1426 : lowerHistoryPathBinding path1426 := by
  apply BindingIds19.pathBinding_from_ids path1426 src1426 [] recs1426 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1426 rfl records1426 rfl
  · intro r hr _
    simp only [recs1426, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise716)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise715)
  · intro r hr _
    simp only [recs1426, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1426] using witness337_projection
    · simpa only [blockWids, path1426] using witness337_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1426 recs1426 records1426 length1426 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
open BindingNumeric20
theorem op180 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,1,1,1,3],[1]) true = bv124 := by
  norm_num [bv124, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op181 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,1,1,1,3],[1]) true = bv498 := by
  norm_num [bv498, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op182 : lowerHistoryPull (lowerHistoryHN) ([1,1,1,1,1,3],[1]) true = bv69 := by
  norm_num [bv69, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op183 : lowerHistoryPull (lowerHistoryH2) ([1,1,1,1,1,3],[1]) true = bv934 := by
  norm_num [bv934, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op184 : lowerHistoryNormalization ([1,1,1,1,1,3,1],[1]) true true = bv330 := by
  norm_num [bv330, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op185 : lowerHistoryNecessary ⟨⟨([3,1,1,1,1,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,1,1,1,3,1],[1]) = some [bv477] := by
  decide +kernel
theorem op186 : lowerHistoryPull (lowerHistoryH7) ([1,1,1,1,1,3,1],[1]) true = bv510 := by
  norm_num [bv510, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op187 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,1,1,1,3,1],[1]) true = bv914 := by
  norm_num [bv914, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op188 : lowerHistoryPull (lowerHistoryHN) ([1,1,1,1,1,3,1],[1]) true = bv68 := by
  norm_num [bv68, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op189 : lowerHistoryPull (lowerHistoryH9) ([1,1,1,1,1],[1]) false = bv778 := by
  norm_num [bv778, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op190 : lowerHistoryNormalization ([1,1,1,1,1,2],[1]) true true = bv361 := by
  norm_num [bv361, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op191 : lowerHistoryNecessary ⟨⟨([3,1,1,1,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,1,1,1,2],[1]) = some [bv496] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def path1427 : LowerHistoryPath := ⟨.initial,341,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,1,1,1,1,3],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩
noncomputable def raw1427 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv331,bv483,bv124,bv498,bv69],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv331,bv483,bv124,bv498,bv69]]
noncomputable def expected1427 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv331,bv483,bv124,bv498,bv69],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv331,bv483,bv124,bv498,bv69]]
theorem structural1427 (ops : RootOps19.SourceOps) (b18 b48 b63 b69 b124 b125 b132 b221 b316 b331 b371 b433 b447 b460 b461 b483 b498 b610 b669 b694 b737 b839 b843 b952 b1079 b1102 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h140 : ops.normalization ([1,1,1],[]) true false = b18)
    (h141 : ops.necessary ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([1,1,1],[]) = some [b694])
    (h142 : ops.pull (lowerHistoryH2) ([1,1,1],[]) true = b1079)
    (h143 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,1],[]) true = b221)
    (h144 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,1],[]) true = b737)
    (h145 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,1],[]) true = b669)
    (h146 : ops.pull (lowerHistoryH23) ([1,1,1],[]) true = b1102)
    (h147 : ops.normalization ([1,1,1,1],[]) true true = b316)
    (h148 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,1,1],[]) = some [b610])
    (h149 : ops.normalization ([1,1,1,1],[1]) false false = b460)
    (h150 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,1,1],[1]) = some [b48])
    (h173 : ops.normalization ([1,1,1,1,1],[1]) false false = b461)
    (h174 : ops.necessary ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,1,1,1],[1]) = some [b63])
    (h177 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,1,1,1],[1]) false = b952)
    (h178 : ops.normalization ([1,1,1,1,1,3],[1]) true true = b331)
    (h179 : ops.necessary ⟨⟨([3,1,1,1,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,1,1,1,3],[1]) = some [b483])
    (h180 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,1,1,1,3],[1]) true = b124)
    (h181 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,1,1,1,3],[1]) true = b498)
    (h182 : ops.pull (lowerHistoryHN) ([1,1,1,1,1,3],[1]) true = b69)
    : RootOps19.eval ops path1427 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b1079,b316,b610,b460,b48,b461,b63,b952,b331,b483,b124,b498,b69],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b221,b737,b669,b1102,b316,b610,b460,b48,b461,b63,b952,b331,b483,b124,b498,b69]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1427, h0, h1, h2, h3, h4, h5, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h173, h174, h177, h178, h179, h180, h181, h182, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1427 : lowerHistorySourcePremises path1427 = raw1427.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1427 RootOps19.actualOps bv18 bv48 bv63 bv69 bv124 bv125 bv132 bv221 bv316 bv331 bv371 bv433 bv447 bv460 bv461 bv483 bv498 bv610 bv669 bv694 bv737 bv839 bv843 bv952 bv1079 bv1102 bv1162 op0 op1 op2 op3 op4 op5 op140 op141 op142 op143 op144 op145 op146 op147 op148 op149 op150 op173 op174 op177 op178 op179 op180 op181 op182
theorem dedup1427 : raw1427.map List.eraseDups = expected1427 := by
  decide +kernel
theorem source1427 : lowerHistorySourcePremises path1427 = expected1427 := (rawSource1427).trans (dedup1427)
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def src1427 : List (List Nat) := [[371,843,433,1162,839,132,447,125,18,694,1079,316,610,460,48,461,63,952,331,483,124,498,69],[371,843,433,1162,839,132,447,125,18,694,221,737,669,1102,316,610,460,48,461,63,952,331,483,124,498,69]]
theorem sourceIDs1427 : lowerHistorySourcePremises path1427 = src1427.map (List.map lowerHistoryBound) := by
  have hb : src1427.map (List.map lowerHistoryBound) = expected1427 := by
    simp only [src1427, expected1427, List.map_cons, List.map_nil, bound18, bound48, bound63, bound69, bound124, bound125, bound132, bound221, bound316, bound331, bound371, bound433, bound447, bound460, bound461, bound483, bound498, bound610, bound669, bound694, bound737, bound839, bound843, bound952, bound1079, bound1102, bound1162]
  exact source1427.trans hb.symm
theorem length1427 : path1427.alternatives = (lowerHistorySourcePremises path1427).length := by
  rw [sourceIDs1427]
  rfl
theorem binding1427 : lowerHistoryPathBinding path1427 := by
  apply BindingIds19.pathBinding_from_ids path1427 src1427 [] recs1427 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1427 rfl records1427 rfl
  · intro r hr _
    simp only [recs1427, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise696)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise695)
  · intro r hr _
    simp only [recs1427, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1427] using witness351_projection
    · simpa only [blockWids, path1427] using witness351_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1427 recs1427 records1427 length1427 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def path1428 : LowerHistoryPath := ⟨.initial,342,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,1,1,1,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩
noncomputable def raw1428 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv331,bv483,bv934,bv330,bv477,bv510,bv914,bv68],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv331,bv483,bv934,bv330,bv477,bv510,bv914,bv68]]
noncomputable def expected1428 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv331,bv483,bv934,bv330,bv477,bv510,bv914,bv68],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv331,bv483,bv934,bv330,bv477,bv510,bv914,bv68]]
theorem structural1428 (ops : RootOps19.SourceOps) (b18 b48 b63 b68 b125 b132 b221 b316 b330 b331 b371 b433 b447 b460 b461 b477 b483 b510 b610 b669 b694 b737 b839 b843 b914 b934 b952 b1079 b1102 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h140 : ops.normalization ([1,1,1],[]) true false = b18)
    (h141 : ops.necessary ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([1,1,1],[]) = some [b694])
    (h142 : ops.pull (lowerHistoryH2) ([1,1,1],[]) true = b1079)
    (h143 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,1],[]) true = b221)
    (h144 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,1],[]) true = b737)
    (h145 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,1],[]) true = b669)
    (h146 : ops.pull (lowerHistoryH23) ([1,1,1],[]) true = b1102)
    (h147 : ops.normalization ([1,1,1,1],[]) true true = b316)
    (h148 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,1,1],[]) = some [b610])
    (h149 : ops.normalization ([1,1,1,1],[1]) false false = b460)
    (h150 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,1,1],[1]) = some [b48])
    (h173 : ops.normalization ([1,1,1,1,1],[1]) false false = b461)
    (h174 : ops.necessary ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,1,1,1],[1]) = some [b63])
    (h177 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,1,1,1],[1]) false = b952)
    (h178 : ops.normalization ([1,1,1,1,1,3],[1]) true true = b331)
    (h179 : ops.necessary ⟨⟨([3,1,1,1,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,1,1,1,3],[1]) = some [b483])
    (h183 : ops.pull (lowerHistoryH2) ([1,1,1,1,1,3],[1]) true = b934)
    (h184 : ops.normalization ([1,1,1,1,1,3,1],[1]) true true = b330)
    (h185 : ops.necessary ⟨⟨([3,1,1,1,1,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,1,1,1,3,1],[1]) = some [b477])
    (h186 : ops.pull (lowerHistoryH7) ([1,1,1,1,1,3,1],[1]) true = b510)
    (h187 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,1,1,1,3,1],[1]) true = b914)
    (h188 : ops.pull (lowerHistoryHN) ([1,1,1,1,1,3,1],[1]) true = b68)
    : RootOps19.eval ops path1428 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b1079,b316,b610,b460,b48,b461,b63,b952,b331,b483,b934,b330,b477,b510,b914,b68],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b221,b737,b669,b1102,b316,b610,b460,b48,b461,b63,b952,b331,b483,b934,b330,b477,b510,b914,b68]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc6 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf6 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1428, h0, h1, h2, h3, h4, h5, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h173, h174, h177, h178, h179, h183, h184, h185, h186, h187, h188, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hf0, hf1, hf2, hf3, hf4, hf5, hf6, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1428 : lowerHistorySourcePremises path1428 = raw1428.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1428 RootOps19.actualOps bv18 bv48 bv63 bv68 bv125 bv132 bv221 bv316 bv330 bv331 bv371 bv433 bv447 bv460 bv461 bv477 bv483 bv510 bv610 bv669 bv694 bv737 bv839 bv843 bv914 bv934 bv952 bv1079 bv1102 bv1162 op0 op1 op2 op3 op4 op5 op140 op141 op142 op143 op144 op145 op146 op147 op148 op149 op150 op173 op174 op177 op178 op179 op183 op184 op185 op186 op187 op188
theorem dedup1428 : raw1428.map List.eraseDups = expected1428 := by
  decide +kernel
theorem source1428 : lowerHistorySourcePremises path1428 = expected1428 := (rawSource1428).trans (dedup1428)
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def src1428 : List (List Nat) := [[371,843,433,1162,839,132,447,125,18,694,1079,316,610,460,48,461,63,952,331,483,934,330,477,510,914,68],[371,843,433,1162,839,132,447,125,18,694,221,737,669,1102,316,610,460,48,461,63,952,331,483,934,330,477,510,914,68]]
theorem sourceIDs1428 : lowerHistorySourcePremises path1428 = src1428.map (List.map lowerHistoryBound) := by
  have hb : src1428.map (List.map lowerHistoryBound) = expected1428 := by
    simp only [src1428, expected1428, List.map_cons, List.map_nil, bound18, bound48, bound63, bound68, bound125, bound132, bound221, bound316, bound330, bound331, bound371, bound433, bound447, bound460, bound461, bound477, bound483, bound510, bound610, bound669, bound694, bound737, bound839, bound843, bound914, bound934, bound952, bound1079, bound1102, bound1162]
  exact source1428.trans hb.symm
theorem length1428 : path1428.alternatives = (lowerHistorySourcePremises path1428).length := by
  rw [sourceIDs1428]
  rfl
theorem binding1428 : lowerHistoryPathBinding path1428 := by
  apply BindingIds19.pathBinding_from_ids path1428 src1428 [] recs1428 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1428 rfl records1428 rfl
  · intro r hr _
    simp only [recs1428, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise694)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise693)
  · intro r hr _
    simp only [recs1428, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1428] using witness434_projection
    · simpa only [blockWids, path1428] using witness434_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1428 recs1428 records1428 length1428 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
open BindingNumeric20
theorem op192 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,1,1,1,2],[1]) true = bv129 := by
  norm_num [bv129, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op193 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,1,1,1,2],[1]) true = bv519 := by
  norm_num [bv519, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op194 : lowerHistoryPull (lowerHistoryHN) ([1,1,1,1,1,2],[1]) true = bv106 := by
  norm_num [bv106, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op195 : lowerHistoryPull (lowerHistoryH2) ([1,1,1,1,1,2],[1]) true = bv950 := by
  norm_num [bv950, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op196 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,1,1,1,2],[1]) true = bv129 := by
  norm_num [bv129, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op197 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,1,1,1,2],[1]) true = bv519 := by
  norm_num [bv519, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op198 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,1,1,1,2],[1]) true = bv484 := by
  norm_num [bv484, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op199 : lowerHistoryPull (lowerHistoryH23) ([1,1,1,1,1,2],[1]) true = bv956 := by
  norm_num [bv956, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op200 : lowerHistoryNormalization ([1,1,1,1,1,2,1],[1]) true true = bv359 := by
  norm_num [bv359, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op201 : lowerHistoryNecessary ⟨⟨([3,1,1,1,1,1,2,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,1,1,1,2,1],[1]) = some [bv482] := by
  decide +kernel
theorem op202 : lowerHistoryPull (lowerHistoryH7) ([1,1,1,1,1,2,1],[1]) true = bv534 := by
  norm_num [bv534, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op203 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,1,1,1,2,1],[1]) true = bv918 := by
  norm_num [bv918, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def path1429 : LowerHistoryPath := ⟨.initial,343,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,1,1,1,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,4⟩
noncomputable def raw1429 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv129,bv519,bv106],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv129,bv519,bv106],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv129,bv519,bv106],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv129,bv519,bv106]]
noncomputable def expected1429 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv129,bv519,bv106],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv129,bv519,bv106],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv129,bv519,bv106],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv129,bv519,bv106]]
theorem structural1429 (ops : RootOps19.SourceOps) (b18 b48 b63 b106 b125 b129 b131 b132 b221 b316 b361 b371 b433 b447 b460 b461 b496 b519 b610 b669 b694 b737 b778 b839 b843 b952 b1079 b1102 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h140 : ops.normalization ([1,1,1],[]) true false = b18)
    (h141 : ops.necessary ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([1,1,1],[]) = some [b694])
    (h142 : ops.pull (lowerHistoryH2) ([1,1,1],[]) true = b1079)
    (h143 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,1],[]) true = b221)
    (h144 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,1],[]) true = b737)
    (h145 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,1],[]) true = b669)
    (h146 : ops.pull (lowerHistoryH23) ([1,1,1],[]) true = b1102)
    (h147 : ops.normalization ([1,1,1,1],[]) true true = b316)
    (h148 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,1,1],[]) = some [b610])
    (h149 : ops.normalization ([1,1,1,1],[1]) false false = b460)
    (h150 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,1,1],[1]) = some [b48])
    (h173 : ops.normalization ([1,1,1,1,1],[1]) false false = b461)
    (h174 : ops.necessary ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,1,1,1],[1]) = some [b63])
    (h177 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,1,1,1],[1]) false = b952)
    (h175 : ops.pull (lowerHistoryH7) ([1,1,1,1,1],[1]) false = b131)
    (h189 : ops.pull (lowerHistoryH9) ([1,1,1,1,1],[1]) false = b778)
    (h190 : ops.normalization ([1,1,1,1,1,2],[1]) true true = b361)
    (h191 : ops.necessary ⟨⟨([3,1,1,1,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,1,1,1,2],[1]) = some [b496])
    (h192 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,1,1,1,2],[1]) true = b129)
    (h193 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,1,1,1,2],[1]) true = b519)
    (h194 : ops.pull (lowerHistoryHN) ([1,1,1,1,1,2],[1]) true = b106)
    : RootOps19.eval ops path1429 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b1079,b316,b610,b460,b48,b461,b63,b952,b361,b496,b129,b519,b106],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b1079,b316,b610,b460,b48,b461,b63,b131,b778,b361,b496,b129,b519,b106],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b221,b737,b669,b1102,b316,b610,b460,b48,b461,b63,b952,b361,b496,b129,b519,b106],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b221,b737,b669,b1102,b316,b610,b460,b48,b461,b63,b131,b778,b361,b496,b129,b519,b106]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1429, h0, h1, h2, h3, h4, h5, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h173, h174, h177, h175, h189, h190, h191, h192, h193, h194, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1429 : lowerHistorySourcePremises path1429 = raw1429.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1429 RootOps19.actualOps bv18 bv48 bv63 bv106 bv125 bv129 bv131 bv132 bv221 bv316 bv361 bv371 bv433 bv447 bv460 bv461 bv496 bv519 bv610 bv669 bv694 bv737 bv778 bv839 bv843 bv952 bv1079 bv1102 bv1162 op0 op1 op2 op3 op4 op5 op140 op141 op142 op143 op144 op145 op146 op147 op148 op149 op150 op173 op174 op177 op175 op189 op190 op191 op192 op193 op194
theorem dedup1429 : raw1429.map List.eraseDups = expected1429 := by
  decide +kernel
theorem source1429 : lowerHistorySourcePremises path1429 = expected1429 := (rawSource1429).trans (dedup1429)
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def src1429 : List (List Nat) := [[371,843,433,1162,839,132,447,125,18,694,1079,316,610,460,48,461,63,952,361,496,129,519,106],[371,843,433,1162,839,132,447,125,18,694,1079,316,610,460,48,461,63,131,778,361,496,129,519,106],[371,843,433,1162,839,132,447,125,18,694,221,737,669,1102,316,610,460,48,461,63,952,361,496,129,519,106],[371,843,433,1162,839,132,447,125,18,694,221,737,669,1102,316,610,460,48,461,63,131,778,361,496,129,519,106]]
theorem sourceIDs1429 : lowerHistorySourcePremises path1429 = src1429.map (List.map lowerHistoryBound) := by
  have hb : src1429.map (List.map lowerHistoryBound) = expected1429 := by
    simp only [src1429, expected1429, List.map_cons, List.map_nil, bound18, bound48, bound63, bound106, bound125, bound129, bound131, bound132, bound221, bound316, bound361, bound371, bound433, bound447, bound460, bound461, bound496, bound519, bound610, bound669, bound694, bound737, bound778, bound839, bound843, bound952, bound1079, bound1102, bound1162]
  exact source1429.trans hb.symm
theorem length1429 : path1429.alternatives = (lowerHistorySourcePremises path1429).length := by
  rw [sourceIDs1429]
  rfl
theorem binding1429 : lowerHistoryPathBinding path1429 := by
  apply BindingIds19.pathBinding_from_ids path1429 src1429 [] recs1429 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1429 rfl records1429 rfl
  · intro r hr _
    simp only [recs1429, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise714)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise712)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise713)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise711)
  · intro r hr _
    simp only [recs1429, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1429] using witness357_projection
    · simpa only [blockWids, path1429] using witness357_projection
    · simpa only [blockWids, path1429] using witness357_projection
    · simpa only [blockWids, path1429] using witness357_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1429 recs1429 records1429 length1429 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
open BindingNumeric20
theorem op204 : lowerHistoryPull (lowerHistoryHN) ([1,1,1,1,1,2,1],[1]) true = bv103 := by
  norm_num [bv103, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def path1430 : LowerHistoryPath := ⟨.initial,344,[3],([1],[]),false,[(([1],[]),false),(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,1,1,1,1,2,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,8⟩
noncomputable def raw1430 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv950,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv129,bv519,bv484,bv956,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv950,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv129,bv519,bv484,bv956,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv950,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv129,bv519,bv484,bv956,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv950,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv129,bv519,bv484,bv956,bv359,bv482,bv534,bv918,bv103]]
noncomputable def expected1430 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv950,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv129,bv519,bv484,bv956,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv950,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv1079,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv129,bv519,bv484,bv956,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv950,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv952,bv361,bv496,bv129,bv519,bv484,bv956,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv950,bv359,bv482,bv534,bv918,bv103],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv18,bv694,bv221,bv737,bv669,bv1102,bv316,bv610,bv460,bv48,bv461,bv63,bv131,bv778,bv361,bv496,bv129,bv519,bv484,bv956,bv359,bv482,bv534,bv918,bv103]]
theorem structural1430 (ops : RootOps19.SourceOps) (b18 b48 b63 b103 b125 b129 b131 b132 b221 b316 b359 b361 b371 b433 b447 b460 b461 b482 b484 b496 b519 b534 b610 b669 b694 b737 b778 b839 b843 b918 b950 b952 b956 b1079 b1102 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h140 : ops.normalization ([1,1,1],[]) true false = b18)
    (h141 : ops.necessary ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([1,1,1],[]) = some [b694])
    (h142 : ops.pull (lowerHistoryH2) ([1,1,1],[]) true = b1079)
    (h143 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,1],[]) true = b221)
    (h144 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,1],[]) true = b737)
    (h145 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,1],[]) true = b669)
    (h146 : ops.pull (lowerHistoryH23) ([1,1,1],[]) true = b1102)
    (h147 : ops.normalization ([1,1,1,1],[]) true true = b316)
    (h148 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,1,1],[]) = some [b610])
    (h149 : ops.normalization ([1,1,1,1],[1]) false false = b460)
    (h150 : ops.necessary ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,1,1],[1]) = some [b48])
    (h173 : ops.normalization ([1,1,1,1,1],[1]) false false = b461)
    (h174 : ops.necessary ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,1,1,1],[1]) = some [b63])
    (h177 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,1,1,1],[1]) false = b952)
    (h175 : ops.pull (lowerHistoryH7) ([1,1,1,1,1],[1]) false = b131)
    (h189 : ops.pull (lowerHistoryH9) ([1,1,1,1,1],[1]) false = b778)
    (h190 : ops.normalization ([1,1,1,1,1,2],[1]) true true = b361)
    (h191 : ops.necessary ⟨⟨([3,1,1,1,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,1,1,1,2],[1]) = some [b496])
    (h195 : ops.pull (lowerHistoryH2) ([1,1,1,1,1,2],[1]) true = b950)
    (h196 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,1,1,1,2],[1]) true = b129)
    (h197 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,1,1,1,2],[1]) true = b519)
    (h198 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,1,1,1,2],[1]) true = b484)
    (h199 : ops.pull (lowerHistoryH23) ([1,1,1,1,1,2],[1]) true = b956)
    (h200 : ops.normalization ([1,1,1,1,1,2,1],[1]) true true = b359)
    (h201 : ops.necessary ⟨⟨([3,1,1,1,1,1,2,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,1,1,1,2,1],[1]) = some [b482])
    (h202 : ops.pull (lowerHistoryH7) ([1,1,1,1,1,2,1],[1]) true = b534)
    (h203 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,1,1,1,2,1],[1]) true = b918)
    (h204 : ops.pull (lowerHistoryHN) ([1,1,1,1,1,2,1],[1]) true = b103)
    : RootOps19.eval ops path1430 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b1079,b316,b610,b460,b48,b461,b63,b952,b361,b496,b950,b359,b482,b534,b918,b103],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b1079,b316,b610,b460,b48,b461,b63,b952,b361,b496,b129,b519,b484,b956,b359,b482,b534,b918,b103],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b1079,b316,b610,b460,b48,b461,b63,b131,b778,b361,b496,b950,b359,b482,b534,b918,b103],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b1079,b316,b610,b460,b48,b461,b63,b131,b778,b361,b496,b129,b519,b484,b956,b359,b482,b534,b918,b103],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b221,b737,b669,b1102,b316,b610,b460,b48,b461,b63,b952,b361,b496,b950,b359,b482,b534,b918,b103],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b221,b737,b669,b1102,b316,b610,b460,b48,b461,b63,b952,b361,b496,b129,b519,b484,b956,b359,b482,b534,b918,b103],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b221,b737,b669,b1102,b316,b610,b460,b48,b461,b63,b131,b778,b361,b496,b950,b359,b482,b534,b918,b103],[b371,b843,b433,b1162,b839,b132,b447,b125,b18,b694,b221,b737,b669,b1102,b316,b610,b460,b48,b461,b63,b131,b778,b361,b496,b129,b519,b484,b956,b359,b482,b534,b918,b103]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,1,1],[3,1,3]),(true,false)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc6 : lowerHistorySourceChoices ⟨⟨([3,1,1,1,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf6 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1430, h0, h1, h2, h3, h4, h5, h140, h141, h142, h143, h144, h145, h146, h147, h148, h149, h150, h173, h174, h177, h175, h189, h190, h191, h195, h196, h197, h198, h199, h200, h201, h202, h203, h204, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hf0, hf1, hf2, hf3, hf4, hf5, hf6, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1430 : lowerHistorySourcePremises path1430 = raw1430.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1430 RootOps19.actualOps bv18 bv48 bv63 bv103 bv125 bv129 bv131 bv132 bv221 bv316 bv359 bv361 bv371 bv433 bv447 bv460 bv461 bv482 bv484 bv496 bv519 bv534 bv610 bv669 bv694 bv737 bv778 bv839 bv843 bv918 bv950 bv952 bv956 bv1079 bv1102 bv1162 op0 op1 op2 op3 op4 op5 op140 op141 op142 op143 op144 op145 op146 op147 op148 op149 op150 op173 op174 op177 op175 op189 op190 op191 op195 op196 op197 op198 op199 op200 op201 op202 op203 op204
theorem dedup1430 : raw1430.map List.eraseDups = expected1430 := by
  decide +kernel
theorem source1430 : lowerHistorySourcePremises path1430 = expected1430 := (rawSource1430).trans (dedup1430)
end M7ContinueSep17.Initial20260918.B1425_1430

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1425_1430
noncomputable def src1430 : List (List Nat) := [[371,843,433,1162,839,132,447,125,18,694,1079,316,610,460,48,461,63,952,361,496,950,359,482,534,918,103],[371,843,433,1162,839,132,447,125,18,694,1079,316,610,460,48,461,63,952,361,496,129,519,484,956,359,482,534,918,103],[371,843,433,1162,839,132,447,125,18,694,1079,316,610,460,48,461,63,131,778,361,496,950,359,482,534,918,103],[371,843,433,1162,839,132,447,125,18,694,1079,316,610,460,48,461,63,131,778,361,496,129,519,484,956,359,482,534,918,103],[371,843,433,1162,839,132,447,125,18,694,221,737,669,1102,316,610,460,48,461,63,952,361,496,950,359,482,534,918,103],[371,843,433,1162,839,132,447,125,18,694,221,737,669,1102,316,610,460,48,461,63,952,361,496,129,519,484,956,359,482,534,918,103],[371,843,433,1162,839,132,447,125,18,694,221,737,669,1102,316,610,460,48,461,63,131,778,361,496,950,359,482,534,918,103],[371,843,433,1162,839,132,447,125,18,694,221,737,669,1102,316,610,460,48,461,63,131,778,361,496,129,519,484,956,359,482,534,918,103]]
theorem sourceIDs1430 : lowerHistorySourcePremises path1430 = src1430.map (List.map lowerHistoryBound) := by
  have hb : src1430.map (List.map lowerHistoryBound) = expected1430 := by
    simp only [src1430, expected1430, List.map_cons, List.map_nil, bound18, bound48, bound63, bound103, bound125, bound129, bound131, bound132, bound221, bound316, bound359, bound361, bound371, bound433, bound447, bound460, bound461, bound482, bound484, bound496, bound519, bound534, bound610, bound669, bound694, bound737, bound778, bound839, bound843, bound918, bound950, bound952, bound956, bound1079, bound1102, bound1162]
  exact source1430.trans hb.symm
theorem length1430 : path1430.alternatives = (lowerHistorySourcePremises path1430).length := by
  rw [sourceIDs1430]
  rfl
theorem binding1430 : lowerHistoryPathBinding path1430 := by
  apply BindingIds19.pathBinding_from_ids path1430 src1430 [] recs1430 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1430 rfl records1430 rfl
  · intro r hr _
    simp only [recs1430, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise710)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise706)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise708)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise704)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise709)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise705)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise707)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise703)
  · intro r hr _
    simp only [recs1430, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1430] using witness440_projection
    · simpa only [blockWids, path1430] using witness440_projection
    · simpa only [blockWids, path1430] using witness440_projection
    · simpa only [blockWids, path1430] using witness440_projection
    · simpa only [blockWids, path1430] using witness440_projection
    · simpa only [blockWids, path1430] using witness440_projection
    · simpa only [blockWids, path1430] using witness440_projection
    · simpa only [blockWids, path1430] using witness440_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1430 recs1430 records1430 length1430 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1425_1430

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
namespace M7ContinueSep17.Initial20260918.B1425_1430
theorem _root_.solution : lowerHistoryBindingBatch 1425 1430 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1425]? = some M7ContinueSep17.Initial20260918.B1425_1430.path1426 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 339 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1426
  · have hl : lowerHistoryPaths[1426]? = some M7ContinueSep17.Initial20260918.B1425_1430.path1427 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 340 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1427
  · have hl : lowerHistoryPaths[1427]? = some M7ContinueSep17.Initial20260918.B1425_1430.path1428 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 341 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1428
  · have hl : lowerHistoryPaths[1428]? = some M7ContinueSep17.Initial20260918.B1425_1430.path1429 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 342 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1429
  · have hl : lowerHistoryPaths[1429]? = some M7ContinueSep17.Initial20260918.B1425_1430.path1430 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 343 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1430
end M7ContinueSep17.Initial20260918.B1425_1430

#print axioms solution
