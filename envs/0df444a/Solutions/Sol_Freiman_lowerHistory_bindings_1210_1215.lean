-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1210_1215
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T05:57:43.993297+00:00
-- url     : https://prove2.me/submissions/73760f2f-97b1-4e37-8165-3dfa95717b31

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
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def bv60 : CertBound := ⟨true,false,⟨⟨(-239829/10233574),(546631/30700722),(0),(0)⟩,⟨(181/314),(1/942),(0),(0)⟩,⟨(823/1417),(-1/1417),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv80 : CertBound := ⟨true,false,⟨⟨(-637821/73117414),(1456879/219352242),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(1508/2593),(-1/2593),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv90 : CertBound := ⟨true,false,⟨⟨(-6281/1259827),(0),(0),(1476/1259827)⟩,⟨(11183/19234),(0),(0),(1/19234)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv105 : CertBound := ⟨true,false,⟨⟨(-47/25670),(0),(0),(91/77010)⟩,⟨(97/170),(0),(0),(1/510)⟩,⟨(881/1510),(0),(0),(-1/1510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv111 : CertBound := ⟨true,false,⟨⟨(-407/422053),(0),(0),(1044/2954371)⟩,⟨(835/1438),(0),(0),(1/10066)⟩,⟨(687/1174),(0),(0),(-1/1174)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv112 : CertBound := ⟨true,false,⟨⟨(-499/635134),(0),(0),(1007/1905402)⟩,⟨(627/1082),(0),(0),(1/3246)⟩,⟨(687/1174),(0),(0),(-1/1174)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv113 : CertBound := ⟨true,false,⟨⟨(-857/1426195),(0),(0),(612/1426195)⟩,⟨(2187/3778),(0),(0),(1/3778)⟩,⟨(881/1510),(0),(0),(-1/1510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv121 : CertBound := ⟨true,false,⟨⟨(19797808150/10032419232121),(213755650/10032419232121),(0),(0)⟩,⟨(179669/309166),(-1/309166),(0),(0)⟩,⟨(66358/114169),(1/114169),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv123 : CertBound := ⟨true,false,⟨⟨(44303371/18134992850),(5790149/9067496425),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(2361/4057),(-1/4057),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv125 : CertBound := ⟨true,false,⟨⟨(157/56212),(1831/84318),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(59/94),(-1/94),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv128 : CertBound := ⟨true,false,⟨⟨(7984397450/1928575040639),(77186750/1928575040639),(0),(0)⟩,⟨(83983/144766),(-1/144766),(0),(0)⟩,⟨(32145/55393),(1/55393),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv132 : CertBound := ⟨true,false,⟨⟨(133/21164),(324/5291),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv192 : CertBound := ⟨true,false,⟨⟨(224300/6577379),(-50/533301),(0),(0)⟩,⟨(1741/3013),(-1/3013),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv202 : CertBound := ⟨true,false,⟨⟨(5983/141700),(279/28340),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv314 : CertBound := ⟨true,true,⟨⟨(-45/697),(0),(0),(14/697)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(53/82),(0),(0),(-1/82)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv315 : CertBound := ⟨true,true,⟨⟨(-249/4454),(0),(0),(65/4454)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv348 : CertBound := ⟨true,true,⟨⟨(-6281/1259827),(0),(0),(1476/1259827)⟩,⟨(11183/19234),(0),(0),(1/19234)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv350 : CertBound := ⟨true,true,⟨⟨(-1627/336670),(0),(0),(1271/1010010)⟩,⟨(1493/2570),(0),(0),(1/7710)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv365 : CertBound := ⟨true,true,⟨⟨(-407/422053),(0),(0),(1044/2954371)⟩,⟨(835/1438),(0),(0),(1/10066)⟩,⟨(687/1174),(0),(0),(-1/1174)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv366 : CertBound := ⟨true,true,⟨⟨(-499/635134),(0),(0),(1007/1905402)⟩,⟨(627/1082),(0),(0),(1/3246)⟩,⟨(687/1174),(0),(0),(-1/1174)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv367 : CertBound := ⟨true,true,⟨⟨(-857/1426195),(0),(0),(612/1426195)⟩,⟨(2187/3778),(0),(0),(1/3778)⟩,⟨(881/1510),(0),(0),(-1/1510)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv433 : CertBound := ⟨true,true,⟨⟨(729/1024),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv447 : CertBound := ⟨false,false,⟨⟨(-3/10),(0),(0),(1/10)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(11/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv458 : CertBound := ⟨false,false,⟨⟨(-73/2227),(0),(0),(28/2227)⟩,⟨(15/34),(0),(0),(1/34)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv462 : CertBound := ⟨false,false,⟨⟨(-15/4454),(0),(0),(37/13362)⟩,⟨(97/170),(0),(0),(1/510)⟩,⟨(157/262),(0),(0),(-1/262)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv468 : CertBound := ⟨false,false,⟨⟨(49133701/86210879833),(36643147/86210879833),(0),(0)⟩,⟨(19888/34189),(-1/34189),(0),(0)⟩,⟨(112835/193969),(1/193969),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv469 : CertBound := ⟨false,false,⟨⟨(22300/32159543),(120751/96478629),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(11655/20053),(-1/20053),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv471 : CertBound := ⟨false,false,⟨⟨(7614572/10230119029),(17550144/10230119029),(0),(0)⟩,⟨(112835/193969),(1/193969),(0),(0)⟩,⟨(2361/4057),(-1/4057),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv472 : CertBound := ⟨false,false,⟨⟨(473425/621449762),(486307/621449762),(0),(0)⟩,⟨(99016/170447),(1/511341),(0),(0)⟩,⟨(11655/20053),(-1/20053),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv478 : CertBound := ⟨false,false,⟨⟨(59235/45743113),(464024/137229339),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(1508/2593),(-1/2593),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv479 : CertBound := ⟨false,false,⟨⟨(104588/76988509),(614405/230965527),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(5606/9661),(-1/9661),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv485 : CertBound := ⟨false,false,⟨⟨(2430659/1401830422),(2446169/1401830422),(0),(0)⟩,⟨(42053/72551),(1/217653),(0),(0)⟩,⟨(5606/9661),(-1/9661),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv490 : CertBound := ⟨false,false,⟨⟨(61674150/30734445313),(-601183950/952767804703),(0),(0)⟩,⟨(54089/92989),(1/92989),(0),(0)⟩,⟨(34959/60094),(-1/60094),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv492 : CertBound := ⟨false,false,⟨⟨(681700000/280962289491),(199289000/2528660605419),(0),(0)⟩,⟨(9070/15613),(1/15613),(0),(0)⟩,⟨(179669/309166),(-1/309166),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv501 : CertBound := ⟨false,false,⟨⟨(101737950/29736883517),(-31913850/29736883517),(0),(0)⟩,⟨(31264/53797),(1/53797),(0),(0)⟩,⟨(20729/35662),(-1/35662),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv504 : CertBound := ⟨false,false,⟨⟨(3135/868621),(18128/2605863),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(823/1417),(-1/1417),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv520 : CertBound := ⟨false,false,⟨⟨(43525316000/8026237234461),(7470775000/72236135110149),(0),(0)⟩,⟨(3861/6661),(1/6661),(0),(0)⟩,⟨(83983/144766),(-1/144766),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv531 : CertBound := ⟨false,false,⟨⟨(537281850/75656770783),(-167837550/75656770783),(0),(0)⟩,⟨(14655/25261),(1/25261),(0),(0)⟩,⟨(10195/17566),(-1/17566),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv559 : CertBound := ⟨false,false,⟨⟨(1253/113206),(2433/113206),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv601 : CertBound := ⟨false,false,⟨⟨(567805/28339588),(394237/28339588),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(7895/13393),(-1/13393),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv604 : CertBound := ⟨false,false,⟨⟨(101/4922),(857/14766),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv681 : CertBound := ⟨false,false,⟨⟨(259000/4995117),(-623500/464545881),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(241/409),(-1/409),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(66/179),(-1/537),(0),(0)⟩⟩⟩
noncomputable def bv713 : CertBound := ⟨false,false,⟨⟨(196101/2393339),(-104261/2393339),(0),(0)⟩,⟨(1508/2593),(-1/2593),(0),(0)⟩,⟨(43/71),(-1/71),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv839 : CertBound := ⟨false,false,⟨⟨(9/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv840 : CertBound := ⟨false,false,⟨⟨(21/23),(-32/69),(0),(0)⟩,⟨(0),(1/3),(0),(0)⟩,⟨(13/23),(1/69),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv911 : CertBound := ⟨false,true,⟨⟨(697098/2794040483),(1362859/8382121449),(0),(0)⟩,⟨(54089/92989),(1/92989),(0),(0)⟩,⟨(34959/60094),(-1/60094),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv912 : CertBound := ⟨false,true,⟨⟨(409314/959254307),(799867/2877762921),(0),(0)⟩,⟨(31264/53797),(1/53797),(0),(0)⟩,⟨(20729/35662),(-1/35662),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv917 : CertBound := ⟨false,true,⟨⟨(197562/221867363),(385771/665602089),(0),(0)⟩,⟨(14655/25261),(1/25261),(0),(0)⟩,⟨(10195/17566),(-1/17566),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv920 : CertBound := ⟨false,true,⟨⟨(373484098850/324567657925043),(4261588550/324567657925043),(0),(0)⟩,⟨(311307/535198),(-1/535198),(0),(0)⟩,⟨(112835/193969),(1/193969),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv928 : CertBound := ⟨false,true,⟨⟨(19797808150/10032419232121),(213755650/10032419232121),(0),(0)⟩,⟨(179669/309166),(-1/309166),(0),(0)⟩,⟨(66358/114169),(1/114169),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv933 : CertBound := ⟨false,true,⟨⟨(44303371/18134992850),(5790149/9067496425),(0),(0)⟩,⟨(306/529),(1/529),(0),(0)⟩,⟨(2361/4057),(-1/4057),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv936 : CertBound := ⟨false,true,⟨⟨(55035250/19477022357),(-2157250/19477022357),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(179669/309166),(-1/309166),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv948 : CertBound := ⟨false,true,⟨⟨(7984397450/1928575040639),(77186750/1928575040639),(0),(0)⟩,⟨(83983/144766),(-1/144766),(0),(0)⟩,⟨(32145/55393),(1/55393),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv955 : CertBound := ⟨false,true,⟨⟨(6429432250/1042313969489),(-415410250/1042313969489),(0),(0)⟩,⟨(711/1226),(1/3678),(0),(0)⟩,⟨(83983/144766),(-1/144766),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1038 : CertBound := ⟨false,true,⟨⟨(224300/6577379),(-50/533301),(0),(0)⟩,⟨(1741/3013),(-1/3013),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1052 : CertBound := ⟨false,true,⟨⟨(5983/141700),(279/28340),(0),(0)⟩,⟨(60/109),(1/109),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1062 : CertBound := ⟨false,true,⟨⟨(9250/188623),(-500/188623),(0),(0)⟩,⟨(1577/2714),(1/8142),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv1162 : CertBound := ⟨false,true,⟨⟨(225/289),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [bv371,bv843,bv433,bv1162] := by
  decide +kernel
theorem op1 : ([] : List CertBound) = [] := by
  decide +kernel
theorem op2 : lowerHistoryNormalization ([1],[]) false false = bv839 := by
  norm_num [bv839, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op3 : lowerHistoryNecessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [bv132] := by
  decide +kernel
theorem op4 : lowerHistoryNormalization ([1,1],[]) false false = bv447 := by
  norm_num [bv447, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op5 : lowerHistoryNecessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [bv125] := by
  decide +kernel
theorem op6 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = bv1052 := by
  norm_num [bv1052, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op33 : lowerHistoryPull (lowerHistoryH7) ([1,1],[]) false = bv202 := by
  norm_num [bv202, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op34 : lowerHistoryPull (lowerHistoryH9) ([1,1],[]) false = bv840 := by
  norm_num [bv840, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op35 : lowerHistoryNormalization ([1,1,2],[]) true true = bv314 := by
  norm_num [bv314, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op36 : lowerHistoryNecessary ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [bv604] := by
  decide +kernel
theorem op37 : lowerHistoryPull (lowerHistoryH2) ([1,1,2],[]) true = bv1038 := by
  norm_num [bv1038, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
open BindingNumeric20
theorem op38 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = bv192 := by
  norm_num [bv192, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op39 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = bv681 := by
  norm_num [bv681, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op40 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = bv601 := by
  norm_num [bv601, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op41 : lowerHistoryPull (lowerHistoryH23) ([1,1,2],[]) true = bv1062 := by
  norm_num [bv1062, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op42 : lowerHistoryNormalization ([1,1,2,1],[]) true true = bv315 := by
  norm_num [bv315, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op43 : lowerHistoryNecessary ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [bv559] := by
  decide +kernel
theorem op44 : lowerHistoryNormalization ([1,1,2,1],[1]) false false = bv458 := by
  norm_num [bv458, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op45 : lowerHistoryNecessary ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2,1],[1]) = some [bv60] := by
  decide +kernel
theorem op68 : lowerHistoryNormalization ([1,1,2,1,1],[1]) false false = bv462 := by
  norm_num [bv462, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op69 : lowerHistoryNecessary ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,2,1,1],[1]) = some [bv80] := by
  decide +kernel
theorem op72 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,2,1,1],[1]) false = bv933 := by
  norm_num [bv933, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op73 : lowerHistoryNormalization ([1,1,2,1,1,3],[1]) true true = bv350 := by
  norm_num [bv350, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
open BindingNumeric20
theorem op74 : lowerHistoryNecessary ⟨⟨([2,1,1,2,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,2,1,1,3],[1]) = some [bv471] := by
  decide +kernel
theorem op78 : lowerHistoryPull (lowerHistoryH2) ([1,1,2,1,1,3],[1]) true = bv920 := by
  norm_num [bv920, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op79 : lowerHistoryNormalization ([1,1,2,1,1,3,1],[1]) true true = bv348 := by
  norm_num [bv348, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op80 : lowerHistoryNecessary ⟨⟨([2,1,1,2,1,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1,3,1],[1]) = some [bv468] := by
  decide +kernel
theorem op81 : lowerHistoryPull (lowerHistoryH7) ([1,1,2,1,1,3,1],[1]) true = bv490 := by
  norm_num [bv490, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op82 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1,3,1],[1]) true = bv911 := by
  norm_num [bv911, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op83 : lowerHistoryPull (lowerHistoryHN) ([1,1,2,1,1,3,1],[1]) true = bv90 := by
  norm_num [bv90, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op70 : lowerHistoryPull (lowerHistoryH7) ([1,1,2,1,1],[1]) false = bv123 := by
  norm_num [bv123, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op84 : lowerHistoryPull (lowerHistoryH9) ([1,1,2,1,1],[1]) false = bv713 := by
  norm_num [bv713, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op85 : lowerHistoryNormalization ([1,1,2,1,1,2],[1]) true true = bv366 := by
  norm_num [bv366, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op86 : lowerHistoryNecessary ⟨⟨([2,1,1,2,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,2,1,1,2],[1]) = some [bv478] := by
  decide +kernel
theorem op87 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,2,1,1,2],[1]) true = bv121 := by
  norm_num [bv121, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def path1211 : LowerHistoryPath := ⟨.initial,125,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,1,1,2,1,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,4⟩
noncomputable def raw1211 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv350,bv471,bv920,bv348,bv468,bv490,bv911,bv90],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv350,bv471,bv920,bv348,bv468,bv490,bv911,bv90],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv350,bv471,bv920,bv348,bv468,bv490,bv911,bv90],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv350,bv471,bv920,bv348,bv468,bv490,bv911,bv90]]
noncomputable def expected1211 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv350,bv471,bv920,bv348,bv468,bv490,bv911,bv90],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv350,bv471,bv920,bv348,bv468,bv490,bv911,bv90],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv350,bv471,bv920,bv348,bv468,bv490,bv911,bv90],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv350,bv471,bv920,bv348,bv468,bv490,bv911,bv90]]
theorem structural1211 (ops : RootOps19.SourceOps) (b60 b80 b90 b125 b132 b192 b202 b314 b315 b348 b350 b371 b433 b447 b458 b462 b468 b471 b490 b559 b601 b604 b681 b839 b840 b843 b911 b920 b933 b1038 b1052 b1062 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h33 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h34 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h35 : ops.normalization ([1,1,2],[]) true true = b314)
    (h36 : ops.necessary ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h37 : ops.pull (lowerHistoryH2) ([1,1,2],[]) true = b1038)
    (h38 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = b192)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = b681)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = b601)
    (h41 : ops.pull (lowerHistoryH23) ([1,1,2],[]) true = b1062)
    (h42 : ops.normalization ([1,1,2,1],[]) true true = b315)
    (h43 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [b559])
    (h44 : ops.normalization ([1,1,2,1],[1]) false false = b458)
    (h45 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2,1],[1]) = some [b60])
    (h68 : ops.normalization ([1,1,2,1,1],[1]) false false = b462)
    (h69 : ops.necessary ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,2,1,1],[1]) = some [b80])
    (h72 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,2,1,1],[1]) false = b933)
    (h73 : ops.normalization ([1,1,2,1,1,3],[1]) true true = b350)
    (h74 : ops.necessary ⟨⟨([2,1,1,2,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,1,2,1,1,3],[1]) = some [b471])
    (h78 : ops.pull (lowerHistoryH2) ([1,1,2,1,1,3],[1]) true = b920)
    (h79 : ops.normalization ([1,1,2,1,1,3,1],[1]) true true = b348)
    (h80 : ops.necessary ⟨⟨([2,1,1,2,1,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1,3,1],[1]) = some [b468])
    (h81 : ops.pull (lowerHistoryH7) ([1,1,2,1,1,3,1],[1]) true = b490)
    (h82 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1,3,1],[1]) true = b911)
    (h83 : ops.pull (lowerHistoryHN) ([1,1,2,1,1,3,1],[1]) true = b90)
    : RootOps19.eval ops path1211 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b933,b350,b471,b920,b348,b468,b490,b911,b90],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b933,b350,b471,b920,b348,b468,b490,b911,b90],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b933,b350,b471,b920,b348,b468,b490,b911,b90],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b933,b350,b471,b920,b348,b468,b490,b911,b90]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc6 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf6 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1211, h0, h1, h2, h3, h4, h5, h6, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h68, h69, h72, h73, h74, h78, h79, h80, h81, h82, h83, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hf0, hf1, hf2, hf3, hf4, hf5, hf6, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1211 : lowerHistorySourcePremises path1211 = raw1211.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1211 RootOps19.actualOps bv60 bv80 bv90 bv125 bv132 bv192 bv202 bv314 bv315 bv348 bv350 bv371 bv433 bv447 bv458 bv462 bv468 bv471 bv490 bv559 bv601 bv604 bv681 bv839 bv840 bv843 bv911 bv920 bv933 bv1038 bv1052 bv1062 bv1162 op0 op1 op2 op3 op4 op5 op6 op33 op34 op35 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op68 op69 op72 op73 op74 op78 op79 op80 op81 op82 op83
theorem dedup1211 : raw1211.map List.eraseDups = expected1211 := by
  decide +kernel
theorem source1211 : lowerHistorySourcePremises path1211 = expected1211 := (rawSource1211).trans (dedup1211)
end M7ContinueSep17.Initial20260918.B1210_1215

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
namespace M7ContinueSep17.Initial20260918.B1210_1215
theorem bound60 : lowerHistoryBound 60 = bv60 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[59]? = some bv60 := Eq.refl (some bv60)
  exact (BoundCompact16.global_to_chunk1 59 (by decide)).trans hl
theorem bound80 : lowerHistoryBound 80 = bv80 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[79]? = some bv80 := Eq.refl (some bv80)
  exact (BoundCompact16.global_to_chunk1 79 (by decide)).trans hl
theorem bound90 : lowerHistoryBound 90 = bv90 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[89]? = some bv90 := Eq.refl (some bv90)
  exact (BoundCompact16.global_to_chunk1 89 (by decide)).trans hl
theorem bound105 : lowerHistoryBound 105 = bv105 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[104]? = some bv105 := Eq.refl (some bv105)
  exact (BoundCompact16.global_to_chunk1 104 (by decide)).trans hl
theorem bound111 : lowerHistoryBound 111 = bv111 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[110]? = some bv111 := Eq.refl (some bv111)
  exact (BoundCompact16.global_to_chunk1 110 (by decide)).trans hl
theorem bound112 : lowerHistoryBound 112 = bv112 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[111]? = some bv112 := Eq.refl (some bv112)
  exact (BoundCompact16.global_to_chunk1 111 (by decide)).trans hl
theorem bound113 : lowerHistoryBound 113 = bv113 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[112]? = some bv113 := Eq.refl (some bv113)
  exact (BoundCompact16.global_to_chunk1 112 (by decide)).trans hl
theorem bound121 : lowerHistoryBound 121 = bv121 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[120]? = some bv121 := Eq.refl (some bv121)
  exact (BoundCompact16.global_to_chunk1 120 (by decide)).trans hl
theorem bound123 : lowerHistoryBound 123 = bv123 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[122]? = some bv123 := Eq.refl (some bv123)
  exact (BoundCompact16.global_to_chunk1 122 (by decide)).trans hl
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
theorem bound348 : lowerHistoryBound 348 = bv348 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[147]? = some bv348 := Eq.refl (some bv348)
  exact (BoundCompact16.global_to_chunk2 147 (by decide)).trans hl
theorem bound350 : lowerHistoryBound 350 = bv350 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[149]? = some bv350 := Eq.refl (some bv350)
  exact (BoundCompact16.global_to_chunk2 149 (by decide)).trans hl
theorem bound365 : lowerHistoryBound 365 = bv365 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[164]? = some bv365 := Eq.refl (some bv365)
  exact (BoundCompact16.global_to_chunk2 164 (by decide)).trans hl
theorem bound366 : lowerHistoryBound 366 = bv366 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[165]? = some bv366 := Eq.refl (some bv366)
  exact (BoundCompact16.global_to_chunk2 165 (by decide)).trans hl
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
theorem bound462 : lowerHistoryBound 462 = bv462 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[61]? = some bv462 := Eq.refl (some bv462)
  exact (BoundCompact16.global_to_chunk3 61 (by decide)).trans hl
theorem bound468 : lowerHistoryBound 468 = bv468 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[67]? = some bv468 := Eq.refl (some bv468)
  exact (BoundCompact16.global_to_chunk3 67 (by decide)).trans hl
theorem bound469 : lowerHistoryBound 469 = bv469 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[68]? = some bv469 := Eq.refl (some bv469)
  exact (BoundCompact16.global_to_chunk3 68 (by decide)).trans hl
theorem bound471 : lowerHistoryBound 471 = bv471 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[70]? = some bv471 := Eq.refl (some bv471)
  exact (BoundCompact16.global_to_chunk3 70 (by decide)).trans hl
theorem bound472 : lowerHistoryBound 472 = bv472 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[71]? = some bv472 := Eq.refl (some bv472)
  exact (BoundCompact16.global_to_chunk3 71 (by decide)).trans hl
theorem bound478 : lowerHistoryBound 478 = bv478 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[77]? = some bv478 := Eq.refl (some bv478)
  exact (BoundCompact16.global_to_chunk3 77 (by decide)).trans hl
theorem bound479 : lowerHistoryBound 479 = bv479 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[78]? = some bv479 := Eq.refl (some bv479)
  exact (BoundCompact16.global_to_chunk3 78 (by decide)).trans hl
theorem bound485 : lowerHistoryBound 485 = bv485 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[84]? = some bv485 := Eq.refl (some bv485)
  exact (BoundCompact16.global_to_chunk3 84 (by decide)).trans hl
theorem bound490 : lowerHistoryBound 490 = bv490 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[89]? = some bv490 := Eq.refl (some bv490)
  exact (BoundCompact16.global_to_chunk3 89 (by decide)).trans hl
theorem bound492 : lowerHistoryBound 492 = bv492 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[91]? = some bv492 := Eq.refl (some bv492)
  exact (BoundCompact16.global_to_chunk3 91 (by decide)).trans hl
theorem bound501 : lowerHistoryBound 501 = bv501 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[100]? = some bv501 := Eq.refl (some bv501)
  exact (BoundCompact16.global_to_chunk3 100 (by decide)).trans hl
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
theorem bound559 : lowerHistoryBound 559 = bv559 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[158]? = some bv559 := Eq.refl (some bv559)
  exact (BoundCompact16.global_to_chunk3 158 (by decide)).trans hl
theorem bound601 : lowerHistoryBound 601 = bv601 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[0]? = some bv601 := Eq.refl (some bv601)
  exact (BoundCompact16.global_to_chunk4 0 (by decide)).trans hl
theorem bound604 : lowerHistoryBound 604 = bv604 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[3]? = some bv604 := Eq.refl (some bv604)
  exact (BoundCompact16.global_to_chunk4 3 (by decide)).trans hl
theorem bound681 : lowerHistoryBound 681 = bv681 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[80]? = some bv681 := Eq.refl (some bv681)
  exact (BoundCompact16.global_to_chunk4 80 (by decide)).trans hl
theorem bound713 : lowerHistoryBound 713 = bv713 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[112]? = some bv713 := Eq.refl (some bv713)
  exact (BoundCompact16.global_to_chunk4 112 (by decide)).trans hl
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
theorem bound911 : lowerHistoryBound 911 = bv911 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[110]? = some bv911 := Eq.refl (some bv911)
  exact (BoundCompact16.global_to_chunk5 110 (by decide)).trans hl
theorem bound912 : lowerHistoryBound 912 = bv912 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[111]? = some bv912 := Eq.refl (some bv912)
  exact (BoundCompact16.global_to_chunk5 111 (by decide)).trans hl
theorem bound917 : lowerHistoryBound 917 = bv917 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[116]? = some bv917 := Eq.refl (some bv917)
  exact (BoundCompact16.global_to_chunk5 116 (by decide)).trans hl
theorem bound920 : lowerHistoryBound 920 = bv920 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[119]? = some bv920 := Eq.refl (some bv920)
  exact (BoundCompact16.global_to_chunk5 119 (by decide)).trans hl
theorem bound928 : lowerHistoryBound 928 = bv928 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[127]? = some bv928 := Eq.refl (some bv928)
  exact (BoundCompact16.global_to_chunk5 127 (by decide)).trans hl
theorem bound933 : lowerHistoryBound 933 = bv933 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[132]? = some bv933 := Eq.refl (some bv933)
  exact (BoundCompact16.global_to_chunk5 132 (by decide)).trans hl
theorem bound936 : lowerHistoryBound 936 = bv936 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[135]? = some bv936 := Eq.refl (some bv936)
  exact (BoundCompact16.global_to_chunk5 135 (by decide)).trans hl
theorem bound948 : lowerHistoryBound 948 = bv948 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[147]? = some bv948 := Eq.refl (some bv948)
  exact (BoundCompact16.global_to_chunk5 147 (by decide)).trans hl
theorem bound955 : lowerHistoryBound 955 = bv955 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[154]? = some bv955 := Eq.refl (some bv955)
  exact (BoundCompact16.global_to_chunk5 154 (by decide)).trans hl
theorem bound1038 : lowerHistoryBound 1038 = bv1038 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[37]? = some bv1038 := Eq.refl (some bv1038)
  exact (BoundCompact16.global_to_chunk6 37).trans hl
theorem bound1052 : lowerHistoryBound 1052 = bv1052 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[51]? = some bv1052 := Eq.refl (some bv1052)
  exact (BoundCompact16.global_to_chunk6 51).trans hl
theorem bound1062 : lowerHistoryBound 1062 = bv1062 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[61]? = some bv1062 := Eq.refl (some bv1062)
  exact (BoundCompact16.global_to_chunk6 61).trans hl
theorem bound1162 : lowerHistoryBound 1162 = bv1162 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[161]? = some bv1162 := Eq.refl (some bv1162)
  exact (BoundCompact16.global_to_chunk6 161).trans hl
end M7ContinueSep17.Initial20260918.B1210_1215

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
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def recs1211 : List LowerHistoryRecord := [⟨.initial,125,0,(-1),false,944,429⟩,⟨.initial,125,1,(-1),false,942,429⟩,⟨.initial,125,2,(-1),false,943,429⟩,⟨.initial,125,3,(-1),false,941,429⟩]
theorem records1211 : lowerHistoryRecordsFor (⟨.initial,125,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,1,1,2,1,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,4⟩ : LowerHistoryPath) = recs1211 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 125)) = recs1211
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1212 : List LowerHistoryRecord := [⟨.initial,126,0,(-1),false,984,350⟩,⟨.initial,126,1,(-1),false,980,350⟩,⟨.initial,126,2,(-1),false,982,350⟩,⟨.initial,126,3,(-1),false,978,350⟩,⟨.initial,126,4,(-1),false,983,350⟩,⟨.initial,126,5,(-1),false,979,350⟩,⟨.initial,126,6,(-1),false,981,350⟩,⟨.initial,126,7,(-1),false,977,350⟩]
theorem records1212 : lowerHistoryRecordsFor (⟨.initial,126,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([2,1,1,2,1,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,8⟩ : LowerHistoryPath) = recs1212 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 126)) = recs1212
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1213 : List LowerHistoryRecord := [⟨.initial,127,0,(-1),false,976,431⟩,⟨.initial,127,1,(-1),false,968,431⟩,⟨.initial,127,2,(-1),false,972,431⟩,⟨.initial,127,3,(-1),false,964,431⟩,⟨.initial,127,4,(-1),false,974,431⟩,⟨.initial,127,5,(-1),false,966,431⟩,⟨.initial,127,6,(-1),false,970,431⟩,⟨.initial,127,7,(-1),false,962,431⟩,⟨.initial,127,8,(-1),false,975,431⟩,⟨.initial,127,9,(-1),false,967,431⟩,⟨.initial,127,10,(-1),false,971,431⟩,⟨.initial,127,11,(-1),false,963,431⟩,⟨.initial,127,12,(-1),false,973,431⟩,⟨.initial,127,13,(-1),false,965,431⟩,⟨.initial,127,14,(-1),false,969,431⟩,⟨.initial,127,15,(-1),false,961,431⟩]
theorem records1213 : lowerHistoryRecordsFor (⟨.initial,127,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,1,1,2,1,1,2,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,16⟩ : LowerHistoryPath) = recs1213 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 127)) = recs1213
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1214 : List LowerHistoryRecord := [⟨.initial,128,0,(-1),false,960,360⟩,⟨.initial,128,1,(-1),false,958,360⟩,⟨.initial,128,2,(-1),false,959,360⟩,⟨.initial,128,3,(-1),false,957,360⟩]
theorem records1214 : lowerHistoryRecordsFor (⟨.initial,128,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([2,1,1,2,1,1,1],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,4⟩ : LowerHistoryPath) = recs1214 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 128)) = recs1214
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1215 : List LowerHistoryRecord := [⟨.initial,129,0,(-1),false,956,439⟩,⟨.initial,129,1,(-1),false,952,439⟩,⟨.initial,129,2,(-1),false,954,439⟩,⟨.initial,129,3,(-1),false,950,439⟩,⟨.initial,129,4,(-1),false,955,439⟩,⟨.initial,129,5,(-1),false,951,439⟩,⟨.initial,129,6,(-1),false,953,439⟩,⟨.initial,129,7,(-1),false,949,439⟩]
theorem records1215 : lowerHistoryRecordsFor (⟨.initial,129,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,1,1,2,1,1,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,8⟩ : LowerHistoryPath) = recs1215 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 129)) = recs1215
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
end M7ContinueSep17.Initial20260918.B1210_1215

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
namespace M7ContinueSep17.Initial20260918.B1210_1215
theorem premise941 : lowerHistoryPremises[940]? = some ([60,80,90,125,132,192,202,314,315,348,350,371,433,447,458,462,468,471,490,559,601,604,681,839,840,843,911,920,933,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[940]? = lowerHistoryPremises05[140]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 140 (by decide)
  exact hg.trans (by rfl)
theorem premise942 : lowerHistoryPremises[941]? = some ([60,80,90,125,132,192,314,315,348,350,371,433,447,458,462,468,471,490,559,601,604,681,839,843,911,920,933,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[941]? = lowerHistoryPremises05[141]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 141 (by decide)
  exact hg.trans (by rfl)
theorem premise943 : lowerHistoryPremises[942]? = some ([60,80,90,125,132,202,314,315,348,350,371,433,447,458,462,468,471,490,559,604,839,840,843,911,920,933,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[942]? = lowerHistoryPremises05[142]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 142 (by decide)
  exact hg.trans (by rfl)
theorem premise944 : lowerHistoryPremises[943]? = some ([60,80,90,125,132,314,315,348,350,371,433,447,458,462,468,471,490,559,604,839,843,911,920,933,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[943]? = lowerHistoryPremises05[143]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 143 (by decide)
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
theorem premise961 : lowerHistoryPremises[960]? = some ([60,80,111,121,123,125,132,192,202,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,601,604,681,713,839,840,843,912,936,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[960]? = lowerHistoryPremises05[160]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 160 (by decide)
  exact hg.trans (by rfl)
theorem premise962 : lowerHistoryPremises[961]? = some ([60,80,111,121,123,125,132,192,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,601,604,681,713,839,843,912,936,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[961]? = lowerHistoryPremises05[161]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 161 (by decide)
  exact hg.trans (by rfl)
theorem premise963 : lowerHistoryPremises[962]? = some ([60,80,111,121,123,125,132,202,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,604,713,839,840,843,912,936,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[962]? = lowerHistoryPremises05[162]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 162 (by decide)
  exact hg.trans (by rfl)
theorem premise964 : lowerHistoryPremises[963]? = some ([60,80,111,121,123,125,132,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,604,713,839,843,912,936,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[963]? = lowerHistoryPremises05[163]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 163 (by decide)
  exact hg.trans (by rfl)
theorem premise965 : lowerHistoryPremises[964]? = some ([60,80,111,121,125,132,192,202,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,601,604,681,839,840,843,912,933,936,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[964]? = lowerHistoryPremises05[164]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 164 (by decide)
  exact hg.trans (by rfl)
theorem premise966 : lowerHistoryPremises[965]? = some ([60,80,111,121,125,132,192,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,601,604,681,839,843,912,933,936,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[965]? = lowerHistoryPremises05[165]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 165 (by decide)
  exact hg.trans (by rfl)
theorem premise967 : lowerHistoryPremises[966]? = some ([60,80,111,121,125,132,202,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,604,839,840,843,912,933,936,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[966]? = lowerHistoryPremises05[166]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 166 (by decide)
  exact hg.trans (by rfl)
theorem premise968 : lowerHistoryPremises[967]? = some ([60,80,111,121,125,132,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,604,839,843,912,933,936,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[967]? = lowerHistoryPremises05[167]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 167 (by decide)
  exact hg.trans (by rfl)
theorem premise969 : lowerHistoryPremises[968]? = some ([60,80,111,123,125,132,192,202,314,315,365,366,371,433,447,458,462,469,478,501,559,601,604,681,713,839,840,843,912,928,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[968]? = lowerHistoryPremises05[168]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 168 (by decide)
  exact hg.trans (by rfl)
theorem premise970 : lowerHistoryPremises[969]? = some ([60,80,111,123,125,132,192,314,315,365,366,371,433,447,458,462,469,478,501,559,601,604,681,713,839,843,912,928,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[969]? = lowerHistoryPremises05[169]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 169 (by decide)
  exact hg.trans (by rfl)
theorem premise971 : lowerHistoryPremises[970]? = some ([60,80,111,123,125,132,202,314,315,365,366,371,433,447,458,462,469,478,501,559,604,713,839,840,843,912,928,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[970]? = lowerHistoryPremises05[170]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 170 (by decide)
  exact hg.trans (by rfl)
theorem premise972 : lowerHistoryPremises[971]? = some ([60,80,111,123,125,132,314,315,365,366,371,433,447,458,462,469,478,501,559,604,713,839,843,912,928,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[971]? = lowerHistoryPremises05[171]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 171 (by decide)
  exact hg.trans (by rfl)
theorem premise973 : lowerHistoryPremises[972]? = some ([60,80,111,125,132,192,202,314,315,365,366,371,433,447,458,462,469,478,501,559,601,604,681,839,840,843,912,928,933,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[972]? = lowerHistoryPremises05[172]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 172 (by decide)
  exact hg.trans (by rfl)
theorem premise974 : lowerHistoryPremises[973]? = some ([60,80,111,125,132,192,314,315,365,366,371,433,447,458,462,469,478,501,559,601,604,681,839,843,912,928,933,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[973]? = lowerHistoryPremises05[173]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 173 (by decide)
  exact hg.trans (by rfl)
theorem premise975 : lowerHistoryPremises[974]? = some ([60,80,111,125,132,202,314,315,365,366,371,433,447,458,462,469,478,501,559,604,839,840,843,912,928,933,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[974]? = lowerHistoryPremises05[174]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 174 (by decide)
  exact hg.trans (by rfl)
theorem premise976 : lowerHistoryPremises[975]? = some ([60,80,111,125,132,314,315,365,366,371,433,447,458,462,469,478,501,559,604,839,843,912,928,933,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[975]? = lowerHistoryPremises05[175]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 175 (by decide)
  exact hg.trans (by rfl)
theorem premise977 : lowerHistoryPremises[976]? = some ([60,80,112,121,123,125,132,192,202,314,315,366,371,433,447,458,462,478,492,559,601,604,681,713,839,840,843,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[976]? = lowerHistoryPremises05[176]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 176 (by decide)
  exact hg.trans (by rfl)
theorem premise978 : lowerHistoryPremises[977]? = some ([60,80,112,121,123,125,132,192,314,315,366,371,433,447,458,462,478,492,559,601,604,681,713,839,843,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[977]? = lowerHistoryPremises05[177]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 177 (by decide)
  exact hg.trans (by rfl)
theorem premise979 : lowerHistoryPremises[978]? = some ([60,80,112,121,123,125,132,202,314,315,366,371,433,447,458,462,478,492,559,604,713,839,840,843,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[978]? = lowerHistoryPremises05[178]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 178 (by decide)
  exact hg.trans (by rfl)
theorem premise980 : lowerHistoryPremises[979]? = some ([60,80,112,121,123,125,132,314,315,366,371,433,447,458,462,478,492,559,604,713,839,843,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[979]? = lowerHistoryPremises05[179]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 179 (by decide)
  exact hg.trans (by rfl)
theorem premise981 : lowerHistoryPremises[980]? = some ([60,80,112,121,125,132,192,202,314,315,366,371,433,447,458,462,478,492,559,601,604,681,839,840,843,933,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[980]? = lowerHistoryPremises05[180]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 180 (by decide)
  exact hg.trans (by rfl)
theorem premise982 : lowerHistoryPremises[981]? = some ([60,80,112,121,125,132,192,314,315,366,371,433,447,458,462,478,492,559,601,604,681,839,843,933,1052,1062,1162] : List Nat) := by
  have hg : lowerHistoryPremises[981]? = lowerHistoryPremises05[181]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 181 (by decide)
  exact hg.trans (by rfl)
theorem premise983 : lowerHistoryPremises[982]? = some ([60,80,112,121,125,132,202,314,315,366,371,433,447,458,462,478,492,559,604,839,840,843,933,1038,1162] : List Nat) := by
  have hg : lowerHistoryPremises[982]? = lowerHistoryPremises05[182]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 182 (by decide)
  exact hg.trans (by rfl)
theorem premise984 : lowerHistoryPremises[983]? = some ([60,80,112,121,125,132,314,315,366,371,433,447,458,462,478,492,559,604,839,843,933,1038,1052,1162] : List Nat) := by
  have hg : lowerHistoryPremises[983]? = lowerHistoryPremises05[183]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 183 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1210_1215
theorem witness350_projection : (lowerHistoryWitness 350).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 350).upperBound = lowerHistoryBound 492 ∧ (lowerHistoryWitness 350).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[149]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 492, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 492, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[349]? = lowerHistoryWitnesses02[149]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 149 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness360_projection : (lowerHistoryWitness 360).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 360).upperBound = lowerHistoryBound 520 ∧ (lowerHistoryWitness 360).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[159]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 520, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 520, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[359]? = lowerHistoryWitnesses02[159]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 159 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness429_projection : (lowerHistoryWitness 429).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 429).upperBound = lowerHistoryBound 911 ∧ (lowerHistoryWitness 429).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[28]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 911, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 911, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[428]? = lowerHistoryWitnesses03[28]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 28 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness431_projection : (lowerHistoryWitness 431).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 431).upperBound = lowerHistoryBound 912 ∧ (lowerHistoryWitness 431).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[30]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 912, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 912, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[430]? = lowerHistoryWitnesses03[30]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 30 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness439_projection : (lowerHistoryWitness 439).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 439).upperBound = lowerHistoryBound 917 ∧ (lowerHistoryWitness 439).rectangle = (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[38]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 917, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 917, (⟨(1/3),(9/25),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[438]? = lowerHistoryWitnesses03[38]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 38 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 350 => (433,492)
  | 360 => (433,520)
  | 429 => (433,911)
  | 431 => (433,912)
  | 439 => (433,917)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 941 => [60,80,90,125,132,192,202,314,315,348,350,371,433,447,458,462,468,471,490,559,601,604,681,839,840,843,911,920,933,1062,1162]
  | 942 => [60,80,90,125,132,192,314,315,348,350,371,433,447,458,462,468,471,490,559,601,604,681,839,843,911,920,933,1052,1062,1162]
  | 943 => [60,80,90,125,132,202,314,315,348,350,371,433,447,458,462,468,471,490,559,604,839,840,843,911,920,933,1038,1162]
  | 944 => [60,80,90,125,132,314,315,348,350,371,433,447,458,462,468,471,490,559,604,839,843,911,920,933,1038,1052,1162]
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
  | 961 => [60,80,111,121,123,125,132,192,202,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,601,604,681,713,839,840,843,912,936,1062,1162]
  | 962 => [60,80,111,121,123,125,132,192,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,601,604,681,713,839,843,912,936,1052,1062,1162]
  | 963 => [60,80,111,121,123,125,132,202,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,604,713,839,840,843,912,936,1038,1162]
  | 964 => [60,80,111,121,123,125,132,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,604,713,839,843,912,936,1038,1052,1162]
  | 965 => [60,80,111,121,125,132,192,202,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,601,604,681,839,840,843,912,933,936,1062,1162]
  | 966 => [60,80,111,121,125,132,192,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,601,604,681,839,843,912,933,936,1052,1062,1162]
  | 967 => [60,80,111,121,125,132,202,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,604,839,840,843,912,933,936,1038,1162]
  | 968 => [60,80,111,121,125,132,314,315,365,366,371,433,447,458,462,469,472,478,492,501,559,604,839,843,912,933,936,1038,1052,1162]
  | 969 => [60,80,111,123,125,132,192,202,314,315,365,366,371,433,447,458,462,469,478,501,559,601,604,681,713,839,840,843,912,928,1062,1162]
  | 970 => [60,80,111,123,125,132,192,314,315,365,366,371,433,447,458,462,469,478,501,559,601,604,681,713,839,843,912,928,1052,1062,1162]
  | 971 => [60,80,111,123,125,132,202,314,315,365,366,371,433,447,458,462,469,478,501,559,604,713,839,840,843,912,928,1038,1162]
  | 972 => [60,80,111,123,125,132,314,315,365,366,371,433,447,458,462,469,478,501,559,604,713,839,843,912,928,1038,1052,1162]
  | 973 => [60,80,111,125,132,192,202,314,315,365,366,371,433,447,458,462,469,478,501,559,601,604,681,839,840,843,912,928,933,1062,1162]
  | 974 => [60,80,111,125,132,192,314,315,365,366,371,433,447,458,462,469,478,501,559,601,604,681,839,843,912,928,933,1052,1062,1162]
  | 975 => [60,80,111,125,132,202,314,315,365,366,371,433,447,458,462,469,478,501,559,604,839,840,843,912,928,933,1038,1162]
  | 976 => [60,80,111,125,132,314,315,365,366,371,433,447,458,462,469,478,501,559,604,839,843,912,928,933,1038,1052,1162]
  | 977 => [60,80,112,121,123,125,132,192,202,314,315,366,371,433,447,458,462,478,492,559,601,604,681,713,839,840,843,1062,1162]
  | 978 => [60,80,112,121,123,125,132,192,314,315,366,371,433,447,458,462,478,492,559,601,604,681,713,839,843,1052,1062,1162]
  | 979 => [60,80,112,121,123,125,132,202,314,315,366,371,433,447,458,462,478,492,559,604,713,839,840,843,1038,1162]
  | 980 => [60,80,112,121,123,125,132,314,315,366,371,433,447,458,462,478,492,559,604,713,839,843,1038,1052,1162]
  | 981 => [60,80,112,121,125,132,192,202,314,315,366,371,433,447,458,462,478,492,559,601,604,681,839,840,843,933,1062,1162]
  | 982 => [60,80,112,121,125,132,192,314,315,366,371,433,447,458,462,478,492,559,601,604,681,839,843,933,1052,1062,1162]
  | 983 => [60,80,112,121,125,132,202,314,315,366,371,433,447,458,462,478,492,559,604,839,840,843,933,1038,1162]
  | 984 => [60,80,112,121,125,132,314,315,366,371,433,447,458,462,478,492,559,604,839,843,933,1038,1052,1162]
  | _ => []
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def src1211 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,933,350,471,920,348,468,490,911,90],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,933,350,471,920,348,468,490,911,90],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,933,350,471,920,348,468,490,911,90],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,933,350,471,920,348,468,490,911,90]]
theorem sourceIDs1211 : lowerHistorySourcePremises path1211 = src1211.map (List.map lowerHistoryBound) := by
  have hb : src1211.map (List.map lowerHistoryBound) = expected1211 := by
    simp only [src1211, expected1211, List.map_cons, List.map_nil, bound60, bound80, bound90, bound125, bound132, bound192, bound202, bound314, bound315, bound348, bound350, bound371, bound433, bound447, bound458, bound462, bound468, bound471, bound490, bound559, bound601, bound604, bound681, bound839, bound840, bound843, bound911, bound920, bound933, bound1038, bound1052, bound1062, bound1162]
  exact source1211.trans hb.symm
theorem length1211 : path1211.alternatives = (lowerHistorySourcePremises path1211).length := by
  rw [sourceIDs1211]
  rfl
theorem binding1211 : lowerHistoryPathBinding path1211 := by
  apply BindingIds19.pathBinding_from_ids path1211 src1211 [] recs1211 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1211 rfl records1211 rfl
  · intro r hr _
    simp only [recs1211, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise944)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise942)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise943)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise941)
  · intro r hr _
    simp only [recs1211, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1211] using witness429_projection
    · simpa only [blockWids, path1211] using witness429_projection
    · simpa only [blockWids, path1211] using witness429_projection
    · simpa only [blockWids, path1211] using witness429_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1211 recs1211 records1211 length1211 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
open BindingNumeric20
theorem op88 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,2,1,1,2],[1]) true = bv492 := by
  norm_num [bv492, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op89 : lowerHistoryPull (lowerHistoryHN) ([1,1,2,1,1,2],[1]) true = bv112 := by
  norm_num [bv112, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op90 : lowerHistoryPull (lowerHistoryH2) ([1,1,2,1,1,2],[1]) true = bv928 := by
  norm_num [bv928, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op91 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2,1,1,2],[1]) true = bv121 := by
  norm_num [bv121, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op92 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2,1,1,2],[1]) true = bv492 := by
  norm_num [bv492, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op93 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2,1,1,2],[1]) true = bv472 := by
  norm_num [bv472, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op94 : lowerHistoryPull (lowerHistoryH23) ([1,1,2,1,1,2],[1]) true = bv936 := by
  norm_num [bv936, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op95 : lowerHistoryNormalization ([1,1,2,1,1,2,1],[1]) true true = bv365 := by
  norm_num [bv365, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op96 : lowerHistoryNecessary ⟨⟨([2,1,1,2,1,1,2,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1,2,1],[1]) = some [bv469] := by
  decide +kernel
theorem op97 : lowerHistoryPull (lowerHistoryH7) ([1,1,2,1,1,2,1],[1]) true = bv501 := by
  norm_num [bv501, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op98 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1,2,1],[1]) true = bv912 := by
  norm_num [bv912, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op99 : lowerHistoryPull (lowerHistoryHN) ([1,1,2,1,1,2,1],[1]) true = bv111 := by
  norm_num [bv111, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def path1212 : LowerHistoryPath := ⟨.initial,126,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([2,1,1,2,1,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,8⟩
noncomputable def raw1212 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv112]]
noncomputable def expected1212 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv112],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv112]]
theorem structural1212 (ops : RootOps19.SourceOps) (b60 b80 b112 b121 b123 b125 b132 b192 b202 b314 b315 b366 b371 b433 b447 b458 b462 b478 b492 b559 b601 b604 b681 b713 b839 b840 b843 b933 b1038 b1052 b1062 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h33 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h34 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h35 : ops.normalization ([1,1,2],[]) true true = b314)
    (h36 : ops.necessary ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h37 : ops.pull (lowerHistoryH2) ([1,1,2],[]) true = b1038)
    (h38 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = b192)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = b681)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = b601)
    (h41 : ops.pull (lowerHistoryH23) ([1,1,2],[]) true = b1062)
    (h42 : ops.normalization ([1,1,2,1],[]) true true = b315)
    (h43 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [b559])
    (h44 : ops.normalization ([1,1,2,1],[1]) false false = b458)
    (h45 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2,1],[1]) = some [b60])
    (h68 : ops.normalization ([1,1,2,1,1],[1]) false false = b462)
    (h69 : ops.necessary ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,2,1,1],[1]) = some [b80])
    (h72 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,2,1,1],[1]) false = b933)
    (h70 : ops.pull (lowerHistoryH7) ([1,1,2,1,1],[1]) false = b123)
    (h84 : ops.pull (lowerHistoryH9) ([1,1,2,1,1],[1]) false = b713)
    (h85 : ops.normalization ([1,1,2,1,1,2],[1]) true true = b366)
    (h86 : ops.necessary ⟨⟨([2,1,1,2,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,2,1,1,2],[1]) = some [b478])
    (h87 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,2,1,1,2],[1]) true = b121)
    (h88 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,2,1,1,2],[1]) true = b492)
    (h89 : ops.pull (lowerHistoryHN) ([1,1,2,1,1,2],[1]) true = b112)
    : RootOps19.eval ops path1212 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b933,b366,b478,b121,b492,b112],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b121,b492,b112],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b933,b366,b478,b121,b492,b112],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b121,b492,b112],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b933,b366,b478,b121,b492,b112],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b121,b492,b112],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b933,b366,b478,b121,b492,b112],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b121,b492,b112]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1212, h0, h1, h2, h3, h4, h5, h6, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h68, h69, h72, h70, h84, h85, h86, h87, h88, h89, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1212 : lowerHistorySourcePremises path1212 = raw1212.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1212 RootOps19.actualOps bv60 bv80 bv112 bv121 bv123 bv125 bv132 bv192 bv202 bv314 bv315 bv366 bv371 bv433 bv447 bv458 bv462 bv478 bv492 bv559 bv601 bv604 bv681 bv713 bv839 bv840 bv843 bv933 bv1038 bv1052 bv1062 bv1162 op0 op1 op2 op3 op4 op5 op6 op33 op34 op35 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op68 op69 op72 op70 op84 op85 op86 op87 op88 op89
theorem dedup1212 : raw1212.map List.eraseDups = expected1212 := by
  decide +kernel
theorem source1212 : lowerHistorySourcePremises path1212 = expected1212 := (rawSource1212).trans (dedup1212)
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def src1212 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,933,366,478,121,492,112],[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,123,713,366,478,121,492,112],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,933,366,478,121,492,112],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,123,713,366,478,121,492,112],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,933,366,478,121,492,112],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,123,713,366,478,121,492,112],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,933,366,478,121,492,112],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,123,713,366,478,121,492,112]]
theorem sourceIDs1212 : lowerHistorySourcePremises path1212 = src1212.map (List.map lowerHistoryBound) := by
  have hb : src1212.map (List.map lowerHistoryBound) = expected1212 := by
    simp only [src1212, expected1212, List.map_cons, List.map_nil, bound60, bound80, bound112, bound121, bound123, bound125, bound132, bound192, bound202, bound314, bound315, bound366, bound371, bound433, bound447, bound458, bound462, bound478, bound492, bound559, bound601, bound604, bound681, bound713, bound839, bound840, bound843, bound933, bound1038, bound1052, bound1062, bound1162]
  exact source1212.trans hb.symm
theorem length1212 : path1212.alternatives = (lowerHistorySourcePremises path1212).length := by
  rw [sourceIDs1212]
  rfl
theorem binding1212 : lowerHistoryPathBinding path1212 := by
  apply BindingIds19.pathBinding_from_ids path1212 src1212 [] recs1212 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1212 rfl records1212 rfl
  · intro r hr _
    simp only [recs1212, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise984)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise980)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise982)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise978)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise983)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise979)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise981)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise977)
  · intro r hr _
    simp only [recs1212, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1212] using witness350_projection
    · simpa only [blockWids, path1212] using witness350_projection
    · simpa only [blockWids, path1212] using witness350_projection
    · simpa only [blockWids, path1212] using witness350_projection
    · simpa only [blockWids, path1212] using witness350_projection
    · simpa only [blockWids, path1212] using witness350_projection
    · simpa only [blockWids, path1212] using witness350_projection
    · simpa only [blockWids, path1212] using witness350_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1212 recs1212 records1212 length1212 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def path1213 : LowerHistoryPath := ⟨.initial,127,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,1,1,2,1,1,2,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,16⟩
noncomputable def raw1213 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111]]
noncomputable def expected1213 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv933,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv928,bv365,bv469,bv501,bv912,bv111],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv123,bv713,bv366,bv478,bv121,bv492,bv472,bv936,bv365,bv469,bv501,bv912,bv111]]
theorem structural1213 (ops : RootOps19.SourceOps) (b60 b80 b111 b121 b123 b125 b132 b192 b202 b314 b315 b365 b366 b371 b433 b447 b458 b462 b469 b472 b478 b492 b501 b559 b601 b604 b681 b713 b839 b840 b843 b912 b928 b933 b936 b1038 b1052 b1062 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h33 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h34 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h35 : ops.normalization ([1,1,2],[]) true true = b314)
    (h36 : ops.necessary ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h37 : ops.pull (lowerHistoryH2) ([1,1,2],[]) true = b1038)
    (h38 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = b192)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = b681)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = b601)
    (h41 : ops.pull (lowerHistoryH23) ([1,1,2],[]) true = b1062)
    (h42 : ops.normalization ([1,1,2,1],[]) true true = b315)
    (h43 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [b559])
    (h44 : ops.normalization ([1,1,2,1],[1]) false false = b458)
    (h45 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2,1],[1]) = some [b60])
    (h68 : ops.normalization ([1,1,2,1,1],[1]) false false = b462)
    (h69 : ops.necessary ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,2,1,1],[1]) = some [b80])
    (h72 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1,2,1,1],[1]) false = b933)
    (h70 : ops.pull (lowerHistoryH7) ([1,1,2,1,1],[1]) false = b123)
    (h84 : ops.pull (lowerHistoryH9) ([1,1,2,1,1],[1]) false = b713)
    (h85 : ops.normalization ([1,1,2,1,1,2],[1]) true true = b366)
    (h86 : ops.necessary ⟨⟨([2,1,1,2,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,1,2,1,1,2],[1]) = some [b478])
    (h90 : ops.pull (lowerHistoryH2) ([1,1,2,1,1,2],[1]) true = b928)
    (h91 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2,1,1,2],[1]) true = b121)
    (h92 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2,1,1,2],[1]) true = b492)
    (h93 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2,1,1,2],[1]) true = b472)
    (h94 : ops.pull (lowerHistoryH23) ([1,1,2,1,1,2],[1]) true = b936)
    (h95 : ops.normalization ([1,1,2,1,1,2,1],[1]) true true = b365)
    (h96 : ops.necessary ⟨⟨([2,1,1,2,1,1,2,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1,2,1],[1]) = some [b469])
    (h97 : ops.pull (lowerHistoryH7) ([1,1,2,1,1,2,1],[1]) true = b501)
    (h98 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1,2,1],[1]) true = b912)
    (h99 : ops.pull (lowerHistoryHN) ([1,1,2,1,1,2,1],[1]) true = b111)
    : RootOps19.eval ops path1213 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b933,b366,b478,b928,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b933,b366,b478,b121,b492,b472,b936,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b928,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b121,b492,b472,b936,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b933,b366,b478,b928,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b933,b366,b478,b121,b492,b472,b936,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b928,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b121,b492,b472,b936,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b933,b366,b478,b928,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b933,b366,b478,b121,b492,b472,b936,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b928,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b121,b492,b472,b936,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b933,b366,b478,b928,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b933,b366,b478,b121,b492,b472,b936,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b928,b365,b469,b501,b912,b111],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b123,b713,b366,b478,b121,b492,b472,b936,b365,b469,b501,b912,b111]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc6 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf5 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf6 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1213, h0, h1, h2, h3, h4, h5, h6, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h68, h69, h72, h70, h84, h85, h86, h90, h91, h92, h93, h94, h95, h96, h97, h98, h99, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hf0, hf1, hf2, hf3, hf4, hf5, hf6, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1213 : lowerHistorySourcePremises path1213 = raw1213.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1213 RootOps19.actualOps bv60 bv80 bv111 bv121 bv123 bv125 bv132 bv192 bv202 bv314 bv315 bv365 bv366 bv371 bv433 bv447 bv458 bv462 bv469 bv472 bv478 bv492 bv501 bv559 bv601 bv604 bv681 bv713 bv839 bv840 bv843 bv912 bv928 bv933 bv936 bv1038 bv1052 bv1062 bv1162 op0 op1 op2 op3 op4 op5 op6 op33 op34 op35 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op68 op69 op72 op70 op84 op85 op86 op90 op91 op92 op93 op94 op95 op96 op97 op98 op99
theorem dedup1213 : raw1213.map List.eraseDups = expected1213 := by
  decide +kernel
theorem source1213 : lowerHistorySourcePremises path1213 = expected1213 := (rawSource1213).trans (dedup1213)
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def src1213 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,933,366,478,928,365,469,501,912,111],[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,933,366,478,121,492,472,936,365,469,501,912,111],[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,123,713,366,478,928,365,469,501,912,111],[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,123,713,366,478,121,492,472,936,365,469,501,912,111],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,933,366,478,928,365,469,501,912,111],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,933,366,478,121,492,472,936,365,469,501,912,111],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,123,713,366,478,928,365,469,501,912,111],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,123,713,366,478,121,492,472,936,365,469,501,912,111],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,933,366,478,928,365,469,501,912,111],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,933,366,478,121,492,472,936,365,469,501,912,111],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,123,713,366,478,928,365,469,501,912,111],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,123,713,366,478,121,492,472,936,365,469,501,912,111],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,933,366,478,928,365,469,501,912,111],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,933,366,478,121,492,472,936,365,469,501,912,111],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,123,713,366,478,928,365,469,501,912,111],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,123,713,366,478,121,492,472,936,365,469,501,912,111]]
theorem sourceIDs1213 : lowerHistorySourcePremises path1213 = src1213.map (List.map lowerHistoryBound) := by
  have hb : src1213.map (List.map lowerHistoryBound) = expected1213 := by
    simp only [src1213, expected1213, List.map_cons, List.map_nil, bound60, bound80, bound111, bound121, bound123, bound125, bound132, bound192, bound202, bound314, bound315, bound365, bound366, bound371, bound433, bound447, bound458, bound462, bound469, bound472, bound478, bound492, bound501, bound559, bound601, bound604, bound681, bound713, bound839, bound840, bound843, bound912, bound928, bound933, bound936, bound1038, bound1052, bound1062, bound1162]
  exact source1213.trans hb.symm
theorem length1213 : path1213.alternatives = (lowerHistorySourcePremises path1213).length := by
  rw [sourceIDs1213]
  rfl
theorem binding1213 : lowerHistoryPathBinding path1213 := by
  apply BindingIds19.pathBinding_from_ids path1213 src1213 [] recs1213 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1213 rfl records1213 rfl
  · intro r hr _
    simp only [recs1213, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise976)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise968)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise972)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise964)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise974)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise966)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise970)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise962)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise975)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise967)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise971)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise963)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise973)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise965)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise969)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise961)
  · intro r hr _
    simp only [recs1213, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
    · simpa only [blockWids, path1213] using witness431_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1213 recs1213 records1213 length1213 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
open BindingNumeric20
theorem op100 : lowerHistoryNormalization ([1,1,2,1,1,1],[1]) true false = bv105 := by
  norm_num [bv105, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op101 : lowerHistoryNecessary ⟨⟨([2,1,1,2,1,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,2,1,1,1],[1]) = some [bv504] := by
  decide +kernel
theorem op102 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,1,2,1,1,1],[1]) true = bv128 := by
  norm_num [bv128, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op103 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,1,2,1,1,1],[1]) true = bv520 := by
  norm_num [bv520, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op104 : lowerHistoryPull (lowerHistoryHN) ([1,1,2,1,1,1],[1]) true = bv105 := by
  norm_num [bv105, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op105 : lowerHistoryPull (lowerHistoryH2) ([1,1,2,1,1,1],[1]) true = bv948 := by
  norm_num [bv948, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op106 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2,1,1,1],[1]) true = bv128 := by
  norm_num [bv128, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op107 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2,1,1,1],[1]) true = bv520 := by
  norm_num [bv520, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op108 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2,1,1,1],[1]) true = bv485 := by
  norm_num [bv485, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op109 : lowerHistoryPull (lowerHistoryH23) ([1,1,2,1,1,1],[1]) true = bv955 := by
  norm_num [bv955, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op110 : lowerHistoryNormalization ([1,1,2,1,1,1,1],[1]) true true = bv367 := by
  norm_num [bv367, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op111 : lowerHistoryNecessary ⟨⟨([2,1,1,2,1,1,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1,1,1],[1]) = some [bv479] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def path1214 : LowerHistoryPath := ⟨.initial,128,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([2,1,1,2,1,1,1],[3,1,3,1]),(false,true),true,3,⟨(1/3),(9/25),(5/19),(4/15)⟩,4⟩
noncomputable def raw1214 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv105],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv105],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv105],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv105]]
noncomputable def expected1214 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520]]
theorem structural1214 (ops : RootOps19.SourceOps) (b60 b80 b105 b125 b128 b132 b192 b202 b314 b315 b371 b433 b447 b458 b462 b504 b520 b559 b601 b604 b681 b839 b840 b843 b1038 b1052 b1062 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h33 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h34 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h35 : ops.normalization ([1,1,2],[]) true true = b314)
    (h36 : ops.necessary ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h37 : ops.pull (lowerHistoryH2) ([1,1,2],[]) true = b1038)
    (h38 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = b192)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = b681)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = b601)
    (h41 : ops.pull (lowerHistoryH23) ([1,1,2],[]) true = b1062)
    (h42 : ops.normalization ([1,1,2,1],[]) true true = b315)
    (h43 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [b559])
    (h44 : ops.normalization ([1,1,2,1],[1]) false false = b458)
    (h45 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2,1],[1]) = some [b60])
    (h68 : ops.normalization ([1,1,2,1,1],[1]) false false = b462)
    (h69 : ops.necessary ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,2,1,1],[1]) = some [b80])
    (h100 : ops.normalization ([1,1,2,1,1,1],[1]) true false = b105)
    (h101 : ops.necessary ⟨⟨([2,1,1,2,1,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,2,1,1,1],[1]) = some [b504])
    (h102 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,1,2,1,1,1],[1]) true = b128)
    (h103 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,1,2,1,1,1],[1]) true = b520)
    (h104 : ops.pull (lowerHistoryHN) ([1,1,2,1,1,1],[1]) true = b105)
    : RootOps19.eval ops path1214 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b105],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b105],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b105],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b105]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
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
  simp only [RootOps19.eval, path1214, h0, h1, h2, h3, h4, h5, h6, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h68, h69, h100, h101, h102, h103, h104, hc0, hc1, hc2, hc3, hc4, hc5, hf0, hf1, hf2, hf3, hf4, hf5, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1214 : lowerHistorySourcePremises path1214 = raw1214.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1214 RootOps19.actualOps bv60 bv80 bv105 bv125 bv128 bv132 bv192 bv202 bv314 bv315 bv371 bv433 bv447 bv458 bv462 bv504 bv520 bv559 bv601 bv604 bv681 bv839 bv840 bv843 bv1038 bv1052 bv1062 bv1162 op0 op1 op2 op3 op4 op5 op6 op33 op34 op35 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op68 op69 op100 op101 op102 op103 op104
theorem dedup1214 : raw1214.map List.eraseDups = expected1214 := by
  decide +kernel
theorem source1214 : lowerHistorySourcePremises path1214 = expected1214 := (rawSource1214).trans (dedup1214)
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def src1214 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,105,504,128,520],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,128,520],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,105,504,128,520],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,128,520]]
theorem sourceIDs1214 : lowerHistorySourcePremises path1214 = src1214.map (List.map lowerHistoryBound) := by
  have hb : src1214.map (List.map lowerHistoryBound) = expected1214 := by
    simp only [src1214, expected1214, List.map_cons, List.map_nil, bound60, bound80, bound105, bound125, bound128, bound132, bound192, bound202, bound314, bound315, bound371, bound433, bound447, bound458, bound462, bound504, bound520, bound559, bound601, bound604, bound681, bound839, bound840, bound843, bound1038, bound1052, bound1062, bound1162]
  exact source1214.trans hb.symm
theorem length1214 : path1214.alternatives = (lowerHistorySourcePremises path1214).length := by
  rw [sourceIDs1214]
  rfl
theorem binding1214 : lowerHistoryPathBinding path1214 := by
  apply BindingIds19.pathBinding_from_ids path1214 src1214 [] recs1214 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1214 rfl records1214 rfl
  · intro r hr _
    simp only [recs1214, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise960)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise958)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise959)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise957)
  · intro r hr _
    simp only [recs1214, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1214] using witness360_projection
    · simpa only [blockWids, path1214] using witness360_projection
    · simpa only [blockWids, path1214] using witness360_projection
    · simpa only [blockWids, path1214] using witness360_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1214 recs1214 records1214 length1214 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
open BindingNumeric20
theorem op112 : lowerHistoryPull (lowerHistoryH7) ([1,1,2,1,1,1,1],[1]) true = bv531 := by
  norm_num [bv531, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op113 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1,1,1],[1]) true = bv917 := by
  norm_num [bv917, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op114 : lowerHistoryPull (lowerHistoryHN) ([1,1,2,1,1,1,1],[1]) true = bv113 := by
  norm_num [bv113, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def path1215 : LowerHistoryPath := ⟨.initial,129,[2],([1],[]),false,[(([1],[]),false),(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,1,1,2,1,1,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/3),(9/25),(5/19),(4/15)⟩,8⟩
noncomputable def raw1215 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113]]
noncomputable def expected1215 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv1052,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv1038,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv948,bv367,bv479,bv531,bv917,bv113],[bv371,bv843,bv433,bv1162,bv839,bv132,bv447,bv125,bv202,bv840,bv314,bv604,bv192,bv681,bv601,bv1062,bv315,bv559,bv458,bv60,bv462,bv80,bv105,bv504,bv128,bv520,bv485,bv955,bv367,bv479,bv531,bv917,bv113]]
theorem structural1215 (ops : RootOps19.SourceOps) (b60 b80 b105 b113 b125 b128 b132 b192 b202 b314 b315 b367 b371 b433 b447 b458 b462 b479 b485 b504 b520 b531 b559 b601 b604 b681 b839 b840 b843 b917 b948 b955 b1038 b1052 b1062 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h2 : ops.normalization ([1],[]) false false = b839)
    (h3 : ops.necessary ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h4 : ops.normalization ([1,1],[]) false false = b447)
    (h5 : ops.necessary ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([1,1],[]) = some [b125])
    (h6 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,1],[]) false = b1052)
    (h33 : ops.pull (lowerHistoryH7) ([1,1],[]) false = b202)
    (h34 : ops.pull (lowerHistoryH9) ([1,1],[]) false = b840)
    (h35 : ops.normalization ([1,1,2],[]) true true = b314)
    (h36 : ops.necessary ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([1,1,2],[]) = some [b604])
    (h37 : ops.pull (lowerHistoryH2) ([1,1,2],[]) true = b1038)
    (h38 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2],[]) true = b192)
    (h39 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2],[]) true = b681)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2],[]) true = b601)
    (h41 : ops.pull (lowerHistoryH23) ([1,1,2],[]) true = b1062)
    (h42 : ops.normalization ([1,1,2,1],[]) true true = b315)
    (h43 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1,1,2,1],[]) = some [b559])
    (h44 : ops.normalization ([1,1,2,1],[1]) false false = b458)
    (h45 : ops.necessary ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1,1,2,1],[1]) = some [b60])
    (h68 : ops.normalization ([1,1,2,1,1],[1]) false false = b462)
    (h69 : ops.necessary ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,1,2,1,1],[1]) = some [b80])
    (h100 : ops.normalization ([1,1,2,1,1,1],[1]) true false = b105)
    (h101 : ops.necessary ⟨⟨([2,1,1,2,1,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,1,2,1,1,1],[1]) = some [b504])
    (h105 : ops.pull (lowerHistoryH2) ([1,1,2,1,1,1],[1]) true = b948)
    (h106 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,1,2,1,1,1],[1]) true = b128)
    (h107 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,1,2,1,1,1],[1]) true = b520)
    (h108 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,1,2,1,1,1],[1]) true = b485)
    (h109 : ops.pull (lowerHistoryH23) ([1,1,2,1,1,1],[1]) true = b955)
    (h110 : ops.normalization ([1,1,2,1,1,1,1],[1]) true true = b367)
    (h111 : ops.necessary ⟨⟨([2,1,1,2,1,1,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,1,2,1,1,1,1],[1]) = some [b479])
    (h112 : ops.pull (lowerHistoryH7) ([1,1,2,1,1,1,1],[1]) true = b531)
    (h113 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,1,2,1,1,1,1],[1]) true = b917)
    (h114 : ops.pull (lowerHistoryHN) ([1,1,2,1,1,1,1],[1]) true = b113)
    : RootOps19.eval ops path1215 = ([[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b948,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b485,b955,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b948,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b1052,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b485,b955,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b948,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b1038,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b485,b955,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b948,b367,b479,b531,b917,b113],[b371,b843,b433,b1162,b839,b132,b447,b125,b202,b840,b314,b604,b192,b681,b601,b1062,b315,b559,b458,b60,b462,b80,b105,b504,b128,b520,b485,b955,b367,b479,b531,b917,b113]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,1,1],[3,1,3]),(false,false)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,1,1,2],[3,1,3]),(true,false)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3]),(false,false)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1],[3,1,3,1]),(false,true)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc5 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc6 : lowerHistorySourceChoices ⟨⟨([2,1,1,2,1,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
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
  simp only [RootOps19.eval, path1215, h0, h1, h2, h3, h4, h5, h6, h33, h34, h35, h36, h37, h38, h39, h40, h41, h42, h43, h44, h45, h68, h69, h100, h101, h105, h106, h107, h108, h109, h110, h111, h112, h113, h114, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hf0, hf1, hf2, hf3, hf4, hf5, hf6, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1215 : lowerHistorySourcePremises path1215 = raw1215.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1215 RootOps19.actualOps bv60 bv80 bv105 bv113 bv125 bv128 bv132 bv192 bv202 bv314 bv315 bv367 bv371 bv433 bv447 bv458 bv462 bv479 bv485 bv504 bv520 bv531 bv559 bv601 bv604 bv681 bv839 bv840 bv843 bv917 bv948 bv955 bv1038 bv1052 bv1062 bv1162 op0 op1 op2 op3 op4 op5 op6 op33 op34 op35 op36 op37 op38 op39 op40 op41 op42 op43 op44 op45 op68 op69 op100 op101 op105 op106 op107 op108 op109 op110 op111 op112 op113 op114
theorem dedup1215 : raw1215.map List.eraseDups = expected1215 := by
  decide +kernel
theorem source1215 : lowerHistorySourcePremises path1215 = expected1215 := (rawSource1215).trans (dedup1215)
end M7ContinueSep17.Initial20260918.B1210_1215

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1210_1215
noncomputable def src1215 : List (List Nat) := [[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,105,504,948,367,479,531,917,113],[371,843,433,1162,839,132,447,125,1052,314,604,1038,315,559,458,60,462,80,105,504,128,520,485,955,367,479,531,917,113],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,948,367,479,531,917,113],[371,843,433,1162,839,132,447,125,1052,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,128,520,485,955,367,479,531,917,113],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,105,504,948,367,479,531,917,113],[371,843,433,1162,839,132,447,125,202,840,314,604,1038,315,559,458,60,462,80,105,504,128,520,485,955,367,479,531,917,113],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,948,367,479,531,917,113],[371,843,433,1162,839,132,447,125,202,840,314,604,192,681,601,1062,315,559,458,60,462,80,105,504,128,520,485,955,367,479,531,917,113]]
theorem sourceIDs1215 : lowerHistorySourcePremises path1215 = src1215.map (List.map lowerHistoryBound) := by
  have hb : src1215.map (List.map lowerHistoryBound) = expected1215 := by
    simp only [src1215, expected1215, List.map_cons, List.map_nil, bound60, bound80, bound105, bound113, bound125, bound128, bound132, bound192, bound202, bound314, bound315, bound367, bound371, bound433, bound447, bound458, bound462, bound479, bound485, bound504, bound520, bound531, bound559, bound601, bound604, bound681, bound839, bound840, bound843, bound917, bound948, bound955, bound1038, bound1052, bound1062, bound1162]
  exact source1215.trans hb.symm
theorem length1215 : path1215.alternatives = (lowerHistorySourcePremises path1215).length := by
  rw [sourceIDs1215]
  rfl
theorem binding1215 : lowerHistoryPathBinding path1215 := by
  apply BindingIds19.pathBinding_from_ids path1215 src1215 [] recs1215 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1215 rfl records1215 rfl
  · intro r hr _
    simp only [recs1215, List.mem_cons, List.not_mem_nil, or_false] at hr
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
    simp only [recs1215, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1215] using witness439_projection
    · simpa only [blockWids, path1215] using witness439_projection
    · simpa only [blockWids, path1215] using witness439_projection
    · simpa only [blockWids, path1215] using witness439_projection
    · simpa only [blockWids, path1215] using witness439_projection
    · simpa only [blockWids, path1215] using witness439_projection
    · simpa only [blockWids, path1215] using witness439_projection
    · simpa only [blockWids, path1215] using witness439_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1215 recs1215 records1215 length1215 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1210_1215

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
namespace M7ContinueSep17.Initial20260918.B1210_1215
theorem _root_.solution : lowerHistoryBindingBatch 1210 1215 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1210]? = some M7ContinueSep17.Initial20260918.B1210_1215.path1211 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 124 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1211
  · have hl : lowerHistoryPaths[1211]? = some M7ContinueSep17.Initial20260918.B1210_1215.path1212 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 125 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1212
  · have hl : lowerHistoryPaths[1212]? = some M7ContinueSep17.Initial20260918.B1210_1215.path1213 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 126 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1213
  · have hl : lowerHistoryPaths[1213]? = some M7ContinueSep17.Initial20260918.B1210_1215.path1214 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 127 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1214
  · have hl : lowerHistoryPaths[1214]? = some M7ContinueSep17.Initial20260918.B1210_1215.path1215 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 128 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1215
end M7ContinueSep17.Initial20260918.B1210_1215

#print axioms solution
