-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0625_0630
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T01:04:24.599863+00:00
-- url     : https://prove2.me/submissions/26fb4992-5231-4c49-9f8c-e6ad926059b3

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
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def bv3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩⟩⟩
noncomputable def bv5 : CertBound := ⟨true,false,⟨⟨(-4078497/4976303),(3063403/4976303),(0),(0)⟩,⟨(168/409),(1/409),(0),(0)⟩,⟨(223/529),(-1/529),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv7 : CertBound := ⟨true,false,⟨⟨(-2415463/5270749),(1816717/5270749),(0),(0)⟩,⟨(109/251),(1/753),(0),(0)⟩,⟨(402/913),(-1/913),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv8 : CertBound := ⟨true,false,⟨⟨(-1707521/5116787),(1276674/5116787),(0),(0)⟩,⟨(594/1417),(1/1417),(0),(0)⟩,⟨(133/314),(-1/942),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv19 : CertBound := ⟨true,false,⟨⟨(-2957543/15273863),(2209052/15273863),(0),(0)⟩,⟨(363/827),(1/2481),(0),(0)⟩,⟨(709/1606),(-1/1606),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩⟩⟩
noncomputable def bv34 : CertBound := ⟨true,false,⟨⟨(-4541489/36558707),(3402426/36558707),(0),(0)⟩,⟨(1085/2593),(1/2593),(0),(0)⟩,⟨(515/1226),(-1/3678),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv44 : CertBound := ⟨true,false,⟨⟨(-23828949/336004309),(17857876/336004309),(0),(0)⟩,⟨(2000/4561),(1/4561),(0),(0)⟩,⟨(2815/6406),(-1/6406),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv170 : CertBound := ⟨true,false,⟨⟨(9455062/501675655),(23991489/5016756550),(0),(0)⟩,⟨(3135/7153),(1/7153),(0),(0)⟩,⟨(402/913),(-1/913),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv191 : CertBound := ⟨true,false,⟨⟨(299259802/9067496425),(154281327/18134992850),(0),(0)⟩,⟨(1696/4057),(1/4057),(0),(0)⟩,⟨(223/529),(-1/529),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv239 : CertBound := ⟨true,false,⟨⟨(10794293/86578700),(1930959/86578700),(0),(0)⟩,⟨(529/1222),(1/1222),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv250 : CertBound := ⟨true,false,⟨⟨(27904867/127104900),(6016573/127104900),(0),(0)⟩,⟨(89/218),(1/654),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv259 : CertBound := ⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv260 : CertBound := ⟨true,false,⟨⟨(31/100),(0),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv267 : CertBound := ⟨true,false,⟨⟨(462273050/1111577051),(-149450/1111577051),(0),(0)⟩,⟨(1137/2714),(-1/8142),(0),(0)⟩,⟨(1272/3013),(1/3013),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv271 : CertBound := ⟨true,false,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv275 : CertBound := ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv283 : CertBound := ⟨true,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
noncomputable def bv284 : CertBound := ⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv416 : CertBound := ⟨true,true,⟨⟨(339/2227),(0),(0),(-8/2227)⟩,⟨(105/262),(0),(0),(1/262)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv420 : CertBound := ⟨true,true,⟨⟨(387/1394),(0),(0),(19/1394)⟩,⟨(29/82),(0),(0),(1/82)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv422 : CertBound := ⟨true,true,⟨⟨(5/17),(0),(0),(-4/85)⟩,⟨(73/170),(0),(0),(1/510)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv425 : CertBound := ⟨true,true,⟨⟨(363/1010),(0),(0),(-37/1010)⟩,⟨(83/202),(0),(0),(1/202)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv429 : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv436 : CertBound := ⟨true,true,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),(0),(0)⟩,⟨(-1/2),(1/2),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv442 : CertBound := ⟨true,true,⟨⟨(3317/299),(-1683/299),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(1),(-1/3),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv665 : CertBound := ⟨false,false,⟨⟨(1607/35615),(0),(0),(208/35615)⟩,⟨(73/170),(0),(0),(1/510)⟩,⟨(373/838),(0),(0),(-1/838)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv711 : CertBound := ⟨false,false,⟨⟨(887/11135),(0),(0),(112/11135)⟩,⟨(105/262),(0),(0),(1/262)⟩,⟨(73/170),(0),(0),(-1/510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv735 : CertBound := ⟨false,false,⟨⟨(215681/1863433),(162441/1863433),(0),(0)⟩,⟨(402/913),(-1/913),(0),(0)⟩,⟨(761/1727),(1/5181),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv746 : CertBound := ⟨false,false,⟨⟨(100728/735839),(193103/735839),(0),(0)⟩,⟨(89/214),(1/214),(0),(0)⟩,⟨(223/529),(-1/529),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv751 : CertBound := ⟨false,false,⟨⟨(356680/2447159),(867844/2447159),(0),(0)⟩,⟨(761/1727),(1/5181),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv772 : CertBound := ⟨false,false,⟨⟨(2901217/14169794),(2384679/14169794),(0),(0)⟩,⟨(5498/13393),(1/13393),(0),(0)⟩,⟨(223/529),(-1/529),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv780 : CertBound := ⟨false,false,⟨⟨(8171/31993),(22664/31993),(0),(0)⟩,⟨(89/214),(1/214),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv781 : CertBound := ⟨false,false,⟨⟨(1167/4454),(0),(0),(71/4454)⟩,⟨(105/262),(0),(0),(1/262)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv807 : CertBound := ⟨false,false,⟨⟨(13/34),(0),(0),(-7/170)⟩,⟨(73/170),(0),(0),(1/510)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv814 : CertBound := ⟨false,false,⟨⟨(537/1010),(0),(0),(-13/1010)⟩,⟨(83/202),(0),(0),(1/202)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv817 : CertBound := ⟨false,false,⟨⟨(753/1394),(0),(0),(91/1394)⟩,⟨(29/82),(0),(0),(1/82)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv819 : CertBound := ⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv821 : CertBound := ⟨false,false,⟨⟨(47955895000/83153712699),(-16982000/9239301411),(0),(0)⟩,⟨(168/409),(1/409),(0),(0)⟩,⟨(1137/2714),(-1/8142),(0),(0)⟩,⟨(1809/6094),(1/6094),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv834 : CertBound := ⟨false,false,⟨⟨(12011/16798),0,0,(973/50394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
noncomputable def bv836 : CertBound := ⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv841 : CertBound := ⟨false,false,⟨⟨(2879947/3109850),0,0,(120883/3109850)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv856 : CertBound := ⟨false,false,⟨⟨(3/2),(0),(0),(1/10)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv876 : CertBound := ⟨false,false,⟨⟨(3317/299),(-1683/299),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(1),(-1/3),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv880 : CertBound := ⟨false,true,⟨⟨(-6957009/6237506),(6234467/6237506),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv884 : CertBound := ⟨false,true,⟨⟨(-1075846/1002947),(2931611/3008841),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv885 : CertBound := ⟨false,true,⟨⟨(-1367629/1290421),(1248628/1290421),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv893 : CertBound := ⟨false,true,⟨⟨(-13726399/40543789),(23458324/40543789),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv895 : CertBound := ⟨false,true,⟨⟨(-12467855/39114933),(7387071/13038311),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv896 : CertBound := ⟨false,true,⟨⟨(-1399514/4575129),(28175102/50326419),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv1131 : CertBound := ⟨false,true,⟨⟨(28448350/118788241),(9050/118788241),(0),(0)⟩,⟨(6265/14278),(-1/14278),(0),(0)⟩,⟨(761/1727),(1/5181),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1139 : CertBound := ⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv1146 : CertBound := ⟨false,true,⟨⟨(462273050/1111577051),(-149450/1111577051),(0),(0)⟩,⟨(1137/2714),(-1/8142),(0),(0)⟩,⟨(1272/3013),(1/3013),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1149 : CertBound := ⟨false,true,⟨⟨(411421/870758),0,0,(2467/124394)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(6941/16810),0,0,(-1/16810)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv1153 : CertBound := ⟨false,true,⟨⟨(3087972/5986825),(290501/2394730),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1157 : CertBound := ⟨false,true,⟨⟨(19056750/31877287),(-984250/31877287),(0),(0)⟩,⟨(89/214),(1/214),(0),(0)⟩,⟨(1137/2714),(-1/8142),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1175 : CertBound := ⟨false,true,⟨⟨(1163038479/896895659),(-317947186/896895659),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
noncomputable def bv1177 : CertBound := ⟨false,true,⟨⟨(2660286/2032855),(-1468807/4065710),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
noncomputable def bv1179 : CertBound := ⟨false,true,⟨⟨(4160513/3159970),(-579309/1579985),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [bv371,bv843,bv260,bv440] := by
  simpa only [bv371,bv843,bv260,bv440] using BindingNumeric20.initial_base
theorem op121 : lowerHistoryRelaxedGoodness ⟨([3],[3,1]),(false,false)⟩ = some [bv3] := by
  decide +kernel
theorem op2 : lowerHistoryNormalization ([2],[3]) false false = bv856 := by
  norm_num [bv856, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op122 : lowerHistoryNecessary ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [bv21] := by
  decide +kernel
theorem op62 : lowerHistoryPull (lowerHistoryH7) ([2],[3]) false = bv275 := by
  norm_num [bv275, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op63 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = bv442 := by
  norm_num [bv442, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op68 : lowerHistoryNormalization ([2,2],[3,1]) false false = bv817 := by
  norm_num [bv817, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op124 : lowerHistoryNecessary ⟨⟨([3,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [bv5] := by
  decide +kernel
theorem op70 : lowerHistoryPull (lowerHistoryH7) ([2,2],[3,1]) false = bv250 := by
  norm_num [bv250, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op71 : lowerHistoryPull (lowerHistoryHN) ([2,2],[3,1]) false = bv817 := by
  norm_num [bv817, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op72 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = bv1153 := by
  norm_num [bv1153, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op73 : lowerHistoryNormalization ([2,3],[3]) true true = bv425 := by
  norm_num [bv425, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def path626 : LowerHistoryPath := ⟨.right,32,[3],([2],[3]),false,[(([2],[1]),false)],([3,2,2],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩
noncomputable def raw626 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv250,bv817]]
noncomputable def expected626 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv250]]
theorem structural626 (ops : RootOps19.SourceOps) (b3 b5 b21 b250 b260 b275 b371 b440 b442 b817 b843 b856 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h121 : ops.relaxed ⟨([3],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h122 : ops.necessary ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h62 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h63 : ops.pull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = b442)
    (h68 : ops.normalization ([2,2],[3,1]) false false = b817)
    (h124 : ops.necessary ⟨⟨([3,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [b5])
    (h70 : ops.pull (lowerHistoryH7) ([2,2],[3,1]) false = b250)
    (h71 : ops.pull (lowerHistoryHN) ([2,2],[3,1]) false = b817)
    : RootOps19.eval ops path626 = ([[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b817]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[1]) = [[lowerHistoryH7,(lowerHistoryComplement lowerHistoryH9)]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path626, h0, h121, h2, h122, h62, h63, h68, h124, h70, h71, hc0, hf0, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource626 : lowerHistorySourcePremises path626 = raw626.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural626 RootOps19.actualOps bv3 bv5 bv21 bv250 bv260 bv275 bv371 bv440 bv442 bv817 bv843 bv856 op0 op121 op2 op122 op62 op63 op68 op124 op70 op71
theorem dedup626 : raw626.map List.eraseDups = expected626 := by
  decide +kernel
theorem source626 : lowerHistorySourcePremises path626 = expected626 := (rawSource626).trans (dedup626)
end M7ContinueSep17.Noninitial20260918.B625_630

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
namespace M7ContinueSep17.Noninitial20260918.B625_630
theorem bound3 : lowerHistoryBound 3 = bv3 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[2]? = some bv3 := Eq.refl (some bv3)
  exact (BoundCompact16.global_to_chunk1 2 (by decide)).trans hl
theorem bound5 : lowerHistoryBound 5 = bv5 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[4]? = some bv5 := Eq.refl (some bv5)
  exact (BoundCompact16.global_to_chunk1 4 (by decide)).trans hl
theorem bound7 : lowerHistoryBound 7 = bv7 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[6]? = some bv7 := Eq.refl (some bv7)
  exact (BoundCompact16.global_to_chunk1 6 (by decide)).trans hl
theorem bound8 : lowerHistoryBound 8 = bv8 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[7]? = some bv8 := Eq.refl (some bv8)
  exact (BoundCompact16.global_to_chunk1 7 (by decide)).trans hl
theorem bound19 : lowerHistoryBound 19 = bv19 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[18]? = some bv19 := Eq.refl (some bv19)
  exact (BoundCompact16.global_to_chunk1 18 (by decide)).trans hl
theorem bound21 : lowerHistoryBound 21 = bv21 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[20]? = some bv21 := Eq.refl (some bv21)
  exact (BoundCompact16.global_to_chunk1 20 (by decide)).trans hl
theorem bound34 : lowerHistoryBound 34 = bv34 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[33]? = some bv34 := Eq.refl (some bv34)
  exact (BoundCompact16.global_to_chunk1 33 (by decide)).trans hl
theorem bound44 : lowerHistoryBound 44 = bv44 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[43]? = some bv44 := Eq.refl (some bv44)
  exact (BoundCompact16.global_to_chunk1 43 (by decide)).trans hl
theorem bound170 : lowerHistoryBound 170 = bv170 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[169]? = some bv170 := Eq.refl (some bv170)
  exact (BoundCompact16.global_to_chunk1 169 (by decide)).trans hl
theorem bound191 : lowerHistoryBound 191 = bv191 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[190]? = some bv191 := Eq.refl (some bv191)
  exact (BoundCompact16.global_to_chunk1 190 (by decide)).trans hl
theorem bound239 : lowerHistoryBound 239 = bv239 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[38]? = some bv239 := Eq.refl (some bv239)
  exact (BoundCompact16.global_to_chunk2 38 (by decide)).trans hl
theorem bound250 : lowerHistoryBound 250 = bv250 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[49]? = some bv250 := Eq.refl (some bv250)
  exact (BoundCompact16.global_to_chunk2 49 (by decide)).trans hl
theorem bound259 : lowerHistoryBound 259 = bv259 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[58]? = some bv259 := Eq.refl (some bv259)
  exact (BoundCompact16.global_to_chunk2 58 (by decide)).trans hl
theorem bound260 : lowerHistoryBound 260 = bv260 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[59]? = some bv260 := Eq.refl (some bv260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hl
theorem bound267 : lowerHistoryBound 267 = bv267 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[66]? = some bv267 := Eq.refl (some bv267)
  exact (BoundCompact16.global_to_chunk2 66 (by decide)).trans hl
theorem bound271 : lowerHistoryBound 271 = bv271 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[70]? = some bv271 := Eq.refl (some bv271)
  exact (BoundCompact16.global_to_chunk2 70 (by decide)).trans hl
theorem bound275 : lowerHistoryBound 275 = bv275 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[74]? = some bv275 := Eq.refl (some bv275)
  exact (BoundCompact16.global_to_chunk2 74 (by decide)).trans hl
theorem bound283 : lowerHistoryBound 283 = bv283 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[82]? = some bv283 := Eq.refl (some bv283)
  exact (BoundCompact16.global_to_chunk2 82 (by decide)).trans hl
theorem bound284 : lowerHistoryBound 284 = bv284 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[83]? = some bv284 := Eq.refl (some bv284)
  exact (BoundCompact16.global_to_chunk2 83 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound416 : lowerHistoryBound 416 = bv416 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[15]? = some bv416 := Eq.refl (some bv416)
  exact (BoundCompact16.global_to_chunk3 15 (by decide)).trans hl
theorem bound420 : lowerHistoryBound 420 = bv420 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[19]? = some bv420 := Eq.refl (some bv420)
  exact (BoundCompact16.global_to_chunk3 19 (by decide)).trans hl
theorem bound422 : lowerHistoryBound 422 = bv422 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[21]? = some bv422 := Eq.refl (some bv422)
  exact (BoundCompact16.global_to_chunk3 21 (by decide)).trans hl
theorem bound425 : lowerHistoryBound 425 = bv425 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[24]? = some bv425 := Eq.refl (some bv425)
  exact (BoundCompact16.global_to_chunk3 24 (by decide)).trans hl
theorem bound429 : lowerHistoryBound 429 = bv429 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[28]? = some bv429 := Eq.refl (some bv429)
  exact (BoundCompact16.global_to_chunk3 28 (by decide)).trans hl
theorem bound436 : lowerHistoryBound 436 = bv436 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[35]? = some bv436 := Eq.refl (some bv436)
  exact (BoundCompact16.global_to_chunk3 35 (by decide)).trans hl
theorem bound440 : lowerHistoryBound 440 = bv440 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[39]? = some bv440 := Eq.refl (some bv440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hl
theorem bound442 : lowerHistoryBound 442 = bv442 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[41]? = some bv442 := Eq.refl (some bv442)
  exact (BoundCompact16.global_to_chunk3 41 (by decide)).trans hl
theorem bound665 : lowerHistoryBound 665 = bv665 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[64]? = some bv665 := Eq.refl (some bv665)
  exact (BoundCompact16.global_to_chunk4 64 (by decide)).trans hl
theorem bound711 : lowerHistoryBound 711 = bv711 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[110]? = some bv711 := Eq.refl (some bv711)
  exact (BoundCompact16.global_to_chunk4 110 (by decide)).trans hl
theorem bound735 : lowerHistoryBound 735 = bv735 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[134]? = some bv735 := Eq.refl (some bv735)
  exact (BoundCompact16.global_to_chunk4 134 (by decide)).trans hl
theorem bound746 : lowerHistoryBound 746 = bv746 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[145]? = some bv746 := Eq.refl (some bv746)
  exact (BoundCompact16.global_to_chunk4 145 (by decide)).trans hl
theorem bound751 : lowerHistoryBound 751 = bv751 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[150]? = some bv751 := Eq.refl (some bv751)
  exact (BoundCompact16.global_to_chunk4 150 (by decide)).trans hl
theorem bound772 : lowerHistoryBound 772 = bv772 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[171]? = some bv772 := Eq.refl (some bv772)
  exact (BoundCompact16.global_to_chunk4 171 (by decide)).trans hl
theorem bound780 : lowerHistoryBound 780 = bv780 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[179]? = some bv780 := Eq.refl (some bv780)
  exact (BoundCompact16.global_to_chunk4 179 (by decide)).trans hl
theorem bound781 : lowerHistoryBound 781 = bv781 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[180]? = some bv781 := Eq.refl (some bv781)
  exact (BoundCompact16.global_to_chunk4 180 (by decide)).trans hl
theorem bound807 : lowerHistoryBound 807 = bv807 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[6]? = some bv807 := Eq.refl (some bv807)
  exact (BoundCompact16.global_to_chunk5 6 (by decide)).trans hl
theorem bound814 : lowerHistoryBound 814 = bv814 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[13]? = some bv814 := Eq.refl (some bv814)
  exact (BoundCompact16.global_to_chunk5 13 (by decide)).trans hl
theorem bound817 : lowerHistoryBound 817 = bv817 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[16]? = some bv817 := Eq.refl (some bv817)
  exact (BoundCompact16.global_to_chunk5 16 (by decide)).trans hl
theorem bound819 : lowerHistoryBound 819 = bv819 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[18]? = some bv819 := Eq.refl (some bv819)
  exact (BoundCompact16.global_to_chunk5 18 (by decide)).trans hl
theorem bound821 : lowerHistoryBound 821 = bv821 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[20]? = some bv821 := Eq.refl (some bv821)
  exact (BoundCompact16.global_to_chunk5 20 (by decide)).trans hl
theorem bound834 : lowerHistoryBound 834 = bv834 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[33]? = some bv834 := Eq.refl (some bv834)
  exact (BoundCompact16.global_to_chunk5 33 (by decide)).trans hl
theorem bound836 : lowerHistoryBound 836 = bv836 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[35]? = some bv836 := Eq.refl (some bv836)
  exact (BoundCompact16.global_to_chunk5 35 (by decide)).trans hl
theorem bound841 : lowerHistoryBound 841 = bv841 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[40]? = some bv841 := Eq.refl (some bv841)
  exact (BoundCompact16.global_to_chunk5 40 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound856 : lowerHistoryBound 856 = bv856 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[55]? = some bv856 := Eq.refl (some bv856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hl
theorem bound876 : lowerHistoryBound 876 = bv876 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[75]? = some bv876 := Eq.refl (some bv876)
  exact (BoundCompact16.global_to_chunk5 75 (by decide)).trans hl
theorem bound880 : lowerHistoryBound 880 = bv880 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[79]? = some bv880 := Eq.refl (some bv880)
  exact (BoundCompact16.global_to_chunk5 79 (by decide)).trans hl
theorem bound884 : lowerHistoryBound 884 = bv884 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[83]? = some bv884 := Eq.refl (some bv884)
  exact (BoundCompact16.global_to_chunk5 83 (by decide)).trans hl
theorem bound885 : lowerHistoryBound 885 = bv885 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[84]? = some bv885 := Eq.refl (some bv885)
  exact (BoundCompact16.global_to_chunk5 84 (by decide)).trans hl
theorem bound893 : lowerHistoryBound 893 = bv893 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[92]? = some bv893 := Eq.refl (some bv893)
  exact (BoundCompact16.global_to_chunk5 92 (by decide)).trans hl
theorem bound895 : lowerHistoryBound 895 = bv895 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[94]? = some bv895 := Eq.refl (some bv895)
  exact (BoundCompact16.global_to_chunk5 94 (by decide)).trans hl
theorem bound896 : lowerHistoryBound 896 = bv896 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[95]? = some bv896 := Eq.refl (some bv896)
  exact (BoundCompact16.global_to_chunk5 95 (by decide)).trans hl
theorem bound1131 : lowerHistoryBound 1131 = bv1131 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[130]? = some bv1131 := Eq.refl (some bv1131)
  exact (BoundCompact16.global_to_chunk6 130).trans hl
theorem bound1139 : lowerHistoryBound 1139 = bv1139 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[138]? = some bv1139 := Eq.refl (some bv1139)
  exact (BoundCompact16.global_to_chunk6 138).trans hl
theorem bound1146 : lowerHistoryBound 1146 = bv1146 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[145]? = some bv1146 := Eq.refl (some bv1146)
  exact (BoundCompact16.global_to_chunk6 145).trans hl
theorem bound1149 : lowerHistoryBound 1149 = bv1149 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[148]? = some bv1149 := Eq.refl (some bv1149)
  exact (BoundCompact16.global_to_chunk6 148).trans hl
theorem bound1153 : lowerHistoryBound 1153 = bv1153 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[152]? = some bv1153 := Eq.refl (some bv1153)
  exact (BoundCompact16.global_to_chunk6 152).trans hl
theorem bound1157 : lowerHistoryBound 1157 = bv1157 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[156]? = some bv1157 := Eq.refl (some bv1157)
  exact (BoundCompact16.global_to_chunk6 156).trans hl
theorem bound1175 : lowerHistoryBound 1175 = bv1175 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[174]? = some bv1175 := Eq.refl (some bv1175)
  exact (BoundCompact16.global_to_chunk6 174).trans hl
theorem bound1177 : lowerHistoryBound 1177 = bv1177 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[176]? = some bv1177 := Eq.refl (some bv1177)
  exact (BoundCompact16.global_to_chunk6 176).trans hl
theorem bound1179 : lowerHistoryBound 1179 = bv1179 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[178]? = some bv1179 := Eq.refl (some bv1179)
  exact (BoundCompact16.global_to_chunk6 178).trans hl
end M7ContinueSep17.Noninitial20260918.B625_630

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
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def recs626 : List LowerHistoryRecord := [⟨.right,32,0,(-1),false,154,1123⟩]
theorem records626 : lowerHistoryRecordsFor (⟨.right,32,[3],([2],[3]),false,[(([2],[1]),false)],([3,2,2],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs626 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 32)) = recs626
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
noncomputable def recs627 : List LowerHistoryRecord := [⟨.right,33,0,(-1),false,344,635⟩]
theorem records627 : lowerHistoryRecordsFor (⟨.right,33,[3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,2,3,1,1],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs627 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 33)) = recs627
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
noncomputable def recs628 : List LowerHistoryRecord := [⟨.right,34,0,(-1),false,234,767⟩]
theorem records628 : lowerHistoryRecordsFor (⟨.right,34,[3],([2],[3]),false,[(([3],[]),true),(([1],[]),true)],([3,2,3],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs628 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 34)) = recs628
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
noncomputable def recs629 : List LowerHistoryRecord := [⟨.right,35,0,(-1),false,284,671⟩,⟨.right,35,1,(-1),false,282,671⟩,⟨.right,35,2,(-1),false,283,671⟩,⟨.right,35,3,(-1),false,281,671⟩]
theorem records629 : lowerHistoryRecordsFor (⟨.right,35,[3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,2,2,1,1],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩ : LowerHistoryPath) = recs629 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 35)) = recs629
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
noncomputable def recs630 : List LowerHistoryRecord := [⟨.right,36,0,(-1),false,155,1045⟩,⟨.right,36,1,0,false,152,1017⟩,⟨.right,36,1,1,false,140,1017⟩,⟨.right,36,1,2,false,146,541⟩,⟨.right,36,1,3,false,148,1017⟩,⟨.right,36,1,4,false,137,1033⟩,⟨.right,36,1,5,false,134,791⟩,⟨.right,36,1,6,false,135,527⟩,⟨.right,36,1,7,false,136,791⟩,⟨.right,36,1,8,false,150,319⟩,⟨.right,36,1,9,false,138,299⟩,⟨.right,36,1,10,false,142,531⟩,⟨.right,36,1,11,false,143,307⟩,⟨.right,36,1,12,false,151,1033⟩,⟨.right,36,1,13,false,139,800⟩,⟨.right,36,1,14,false,144,535⟩,⟨.right,36,1,15,false,145,804⟩]
theorem records630 : lowerHistoryRecordsFor (⟨.right,36,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),true)],([3,2,2],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs630 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .right).filter (fun r => decide (r.catalog = .right ∧ r.pathId = 36)) = recs630
  rw [M7ContinueSep17.CatalogueGeneral.catalogListR]
  rfl
end M7ContinueSep17.Noninitial20260918.B625_630

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
namespace M7ContinueSep17.Noninitial20260918.B625_630
theorem premise134 : lowerHistoryPremises[133]? = some ([3,5,21,250,259,260,271,275,371,420,440,780,817,834,836,843,856,876,1175] : List Nat) := by
  have hg : lowerHistoryPremises[133]? = lowerHistoryPremises01[133]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 133 (by decide)
  exact hg.trans (by rfl)
theorem premise135 : lowerHistoryPremises[134]? = some ([3,5,21,250,259,260,275,283,371,420,436,440,780,817,836,843,856,876,1179] : List Nat) := by
  have hg : lowerHistoryPremises[134]? = lowerHistoryPremises01[134]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 134 (by decide)
  exact hg.trans (by rfl)
theorem premise136 : lowerHistoryPremises[135]? = some ([3,5,21,250,259,260,275,283,371,420,440,780,817,836,841,843,856,876,1177] : List Nat) := by
  have hg : lowerHistoryPremises[135]? = lowerHistoryPremises01[135]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 135 (by decide)
  exact hg.trans (by rfl)
theorem premise137 : lowerHistoryPremises[136]? = some ([3,5,21,250,259,260,275,371,420,440,780,817,834,836,843,856,876,1149,1179] : List Nat) := by
  have hg : lowerHistoryPremises[136]? = lowerHistoryPremises01[136]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 136 (by decide)
  exact hg.trans (by rfl)
theorem premise138 : lowerHistoryPremises[137]? = some ([3,5,21,250,260,271,275,284,371,420,429,440,780,817,834,843,856,876,880] : List Nat) := by
  have hg : lowerHistoryPremises[137]? = lowerHistoryPremises01[137]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 137 (by decide)
  exact hg.trans (by rfl)
theorem premise139 : lowerHistoryPremises[138]? = some ([3,5,21,250,260,271,275,284,371,420,440,780,817,819,834,843,856,876,893] : List Nat) := by
  have hg : lowerHistoryPremises[138]? = lowerHistoryPremises01[138]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 138 (by decide)
  exact hg.trans (by rfl)
theorem premise140 : lowerHistoryPremises[139]? = some ([3,5,21,250,260,271,275,371,420,440,780,817,834,836,843,856,876,880,1139] : List Nat) := by
  have hg : lowerHistoryPremises[139]? = lowerHistoryPremises01[139]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 139 (by decide)
  exact hg.trans (by rfl)
theorem premise142 : lowerHistoryPremises[141]? = some ([3,5,21,250,260,275,283,284,371,420,429,436,440,780,817,843,856,876,884] : List Nat) := by
  have hg : lowerHistoryPremises[141]? = lowerHistoryPremises01[141]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 141 (by decide)
  exact hg.trans (by rfl)
theorem premise143 : lowerHistoryPremises[142]? = some ([3,5,21,250,260,275,283,284,371,420,429,440,780,817,841,843,856,876,885] : List Nat) := by
  have hg : lowerHistoryPremises[142]? = lowerHistoryPremises01[142]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 142 (by decide)
  exact hg.trans (by rfl)
theorem premise144 : lowerHistoryPremises[143]? = some ([3,5,21,250,260,275,283,284,371,420,436,440,780,817,819,843,856,876,895] : List Nat) := by
  have hg : lowerHistoryPremises[143]? = lowerHistoryPremises01[143]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 143 (by decide)
  exact hg.trans (by rfl)
theorem premise145 : lowerHistoryPremises[144]? = some ([3,5,21,250,260,275,283,284,371,420,440,780,817,819,841,843,856,876,896] : List Nat) := by
  have hg : lowerHistoryPremises[144]? = lowerHistoryPremises01[144]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 144 (by decide)
  exact hg.trans (by rfl)
theorem premise146 : lowerHistoryPremises[145]? = some ([3,5,21,250,260,275,283,371,420,436,440,780,817,836,843,856,876,884,1139] : List Nat) := by
  have hg : lowerHistoryPremises[145]? = lowerHistoryPremises01[145]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 145 (by decide)
  exact hg.trans (by rfl)
theorem premise148 : lowerHistoryPremises[147]? = some ([3,5,21,250,260,275,283,371,420,440,780,817,836,841,843,856,876,885,1139] : List Nat) := by
  have hg : lowerHistoryPremises[147]? = lowerHistoryPremises01[147]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 147 (by decide)
  exact hg.trans (by rfl)
theorem premise150 : lowerHistoryPremises[149]? = some ([3,5,21,250,260,275,284,371,420,429,440,780,817,834,843,856,876,884,1149] : List Nat) := by
  have hg : lowerHistoryPremises[149]? = lowerHistoryPremises01[149]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 149 (by decide)
  exact hg.trans (by rfl)
theorem premise151 : lowerHistoryPremises[150]? = some ([3,5,21,250,260,275,284,371,420,440,780,817,819,834,843,856,876,895,1149] : List Nat) := by
  have hg : lowerHistoryPremises[150]? = lowerHistoryPremises01[150]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 150 (by decide)
  exact hg.trans (by rfl)
theorem premise152 : lowerHistoryPremises[151]? = some ([3,5,21,250,260,275,371,420,440,780,817,834,836,843,856,876,884,1139,1149] : List Nat) := by
  have hg : lowerHistoryPremises[151]? = lowerHistoryPremises01[151]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 151 (by decide)
  exact hg.trans (by rfl)
theorem premise154 : lowerHistoryPremises[153]? = some ([3,5,21,250,260,275,371,440,442,817,843,856] : List Nat) := by
  have hg : lowerHistoryPremises[153]? = lowerHistoryPremises01[153]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 153 (by decide)
  exact hg.trans (by rfl)
theorem premise155 : lowerHistoryPremises[154]? = some ([3,5,21,250,260,371,420,440,780,817,843,856,1153] : List Nat) := by
  have hg : lowerHistoryPremises[154]? = lowerHistoryPremises01[154]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 154 (by decide)
  exact hg.trans (by rfl)
theorem premise234 : lowerHistoryPremises[233]? = some ([3,7,21,239,260,371,425,440,751,814,843,856,1153] : List Nat) := by
  have hg : lowerHistoryPremises[233]? = lowerHistoryPremises02[33]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 33 (by decide)
  exact hg.trans (by rfl)
theorem premise281 : lowerHistoryPremises[280]? = some ([3,8,21,34,191,260,267,275,371,416,420,440,711,746,772,780,781,821,843,856,876,1157] : List Nat) := by
  have hg : lowerHistoryPremises[280]? = lowerHistoryPremises02[80]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 80 (by decide)
  exact hg.trans (by rfl)
theorem premise282 : lowerHistoryPremises[281]? = some ([3,8,21,34,191,260,267,371,416,420,440,711,746,772,780,781,821,843,856,1153,1157] : List Nat) := by
  have hg : lowerHistoryPremises[281]? = lowerHistoryPremises02[81]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 81 (by decide)
  exact hg.trans (by rfl)
theorem premise283 : lowerHistoryPremises[282]? = some ([3,8,21,34,191,260,275,371,416,420,440,711,746,780,781,843,856,876,1146] : List Nat) := by
  have hg : lowerHistoryPremises[282]? = lowerHistoryPremises02[82]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 82 (by decide)
  exact hg.trans (by rfl)
theorem premise284 : lowerHistoryPremises[283]? = some ([3,8,21,34,191,260,371,416,420,440,711,746,780,781,843,856,1146,1153] : List Nat) := by
  have hg : lowerHistoryPremises[283]? = lowerHistoryPremises02[83]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 83 (by decide)
  exact hg.trans (by rfl)
theorem premise344 : lowerHistoryPremises[343]? = some ([3,19,21,44,170,260,371,422,425,440,665,735,751,807,843,856,1131,1153] : List Nat) := by
  have hg : lowerHistoryPremises[343]? = lowerHistoryPremises02[143]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 143 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Noninitial20260918.B625_630
theorem witness299_projection : (lowerHistoryWitness 299).lowerBound = lowerHistoryBound 429 ∧ (lowerHistoryWitness 299).upperBound = lowerHistoryBound 880 ∧ (lowerHistoryWitness 299).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[98]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 429, lowerHistoryBound 880, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 429, lowerHistoryBound 880, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[298]? = lowerHistoryWitnesses02[98]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 98 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness307_projection : (lowerHistoryWitness 307).lowerBound = lowerHistoryBound 429 ∧ (lowerHistoryWitness 307).upperBound = lowerHistoryBound 885 ∧ (lowerHistoryWitness 307).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[106]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 429, lowerHistoryBound 885, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 429, lowerHistoryBound 885, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[306]? = lowerHistoryWitnesses02[106]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 106 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness319_projection : (lowerHistoryWitness 319).lowerBound = lowerHistoryBound 429 ∧ (lowerHistoryWitness 319).upperBound = lowerHistoryBound 1149 ∧ (lowerHistoryWitness 319).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[118]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 429, lowerHistoryBound 1149, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 429, lowerHistoryBound 1149, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[318]? = lowerHistoryWitnesses02[118]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 118 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness527_projection : (lowerHistoryWitness 527).lowerBound = lowerHistoryBound 436 ∧ (lowerHistoryWitness 527).upperBound = lowerHistoryBound 836 ∧ (lowerHistoryWitness 527).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[126]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 436, lowerHistoryBound 836, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 436, lowerHistoryBound 836, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[526]? = lowerHistoryWitnesses03[126]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 126 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness531_projection : (lowerHistoryWitness 531).lowerBound = lowerHistoryBound 436 ∧ (lowerHistoryWitness 531).upperBound = lowerHistoryBound 884 ∧ (lowerHistoryWitness 531).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[130]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 436, lowerHistoryBound 884, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 436, lowerHistoryBound 884, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[530]? = lowerHistoryWitnesses03[130]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 130 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness535_projection : (lowerHistoryWitness 535).lowerBound = lowerHistoryBound 436 ∧ (lowerHistoryWitness 535).upperBound = lowerHistoryBound 895 ∧ (lowerHistoryWitness 535).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[134]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 436, lowerHistoryBound 895, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 436, lowerHistoryBound 895, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[534]? = lowerHistoryWitnesses03[134]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 134 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness541_projection : (lowerHistoryWitness 541).lowerBound = lowerHistoryBound 436 ∧ (lowerHistoryWitness 541).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 541).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[140]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 436, lowerHistoryBound 1139, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 436, lowerHistoryBound 1139, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[540]? = lowerHistoryWitnesses03[140]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 140 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness635_projection : (lowerHistoryWitness 635).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 635).upperBound = lowerHistoryBound 665 ∧ (lowerHistoryWitness 635).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[34]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 665, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 665, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[634]? = lowerHistoryWitnesses04[34]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 34 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness671_projection : (lowerHistoryWitness 671).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 671).upperBound = lowerHistoryBound 711 ∧ (lowerHistoryWitness 671).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[70]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 711, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 711, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[670]? = lowerHistoryWitnesses04[70]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 70 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness767_projection : (lowerHistoryWitness 767).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 767).upperBound = lowerHistoryBound 814 ∧ (lowerHistoryWitness 767).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[166]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 814, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 814, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[766]? = lowerHistoryWitnesses04[166]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 166 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness791_projection : (lowerHistoryWitness 791).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 791).upperBound = lowerHistoryBound 836 ∧ (lowerHistoryWitness 791).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[190]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 836, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 836, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[790]? = lowerHistoryWitnesses04[190]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 190 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness800_projection : (lowerHistoryWitness 800).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 800).upperBound = lowerHistoryBound 893 ∧ (lowerHistoryWitness 800).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[199]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 893, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 893, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[799]? = lowerHistoryWitnesses04[199]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 199 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness804_projection : (lowerHistoryWitness 804).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 804).upperBound = lowerHistoryBound 896 ∧ (lowerHistoryWitness 804).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[3]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 896, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 896, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[803]? = lowerHistoryWitnesses05[3]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk5 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 3 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1017_projection : (lowerHistoryWitness 1017).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 1017).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 1017).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[16]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 1139, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 1139, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1016]? = lowerHistoryWitnesses06[16]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 16 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1033_projection : (lowerHistoryWitness 1033).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 1033).upperBound = lowerHistoryBound 1149 ∧ (lowerHistoryWitness 1033).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[32]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 1149, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 1149, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1032]? = lowerHistoryWitnesses06[32]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 32 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1045_projection : (lowerHistoryWitness 1045).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 1045).upperBound = lowerHistoryBound 1153 ∧ (lowerHistoryWitness 1045).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[44]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 1153, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 1153, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1044]? = lowerHistoryWitnesses06[44]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 44 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1123_projection : (lowerHistoryWitness 1123).lowerBound = lowerHistoryBound 442 ∧ (lowerHistoryWitness 1123).upperBound = lowerHistoryBound 817 ∧ (lowerHistoryWitness 1123).rectangle = (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[122]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 817, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 817, (⟨(1/4),(1/3),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1122]? = lowerHistoryWitnesses06[122]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 122 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 299 => (429,880)
  | 307 => (429,885)
  | 319 => (429,1149)
  | 527 => (436,836)
  | 531 => (436,884)
  | 535 => (436,895)
  | 541 => (436,1139)
  | 635 => (440,665)
  | 671 => (440,711)
  | 767 => (440,814)
  | 791 => (440,836)
  | 800 => (440,893)
  | 804 => (440,896)
  | 1017 => (440,1139)
  | 1033 => (440,1149)
  | 1045 => (440,1153)
  | 1123 => (442,817)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 134 => [3,5,21,250,259,260,271,275,371,420,440,780,817,834,836,843,856,876,1175]
  | 135 => [3,5,21,250,259,260,275,283,371,420,436,440,780,817,836,843,856,876,1179]
  | 136 => [3,5,21,250,259,260,275,283,371,420,440,780,817,836,841,843,856,876,1177]
  | 137 => [3,5,21,250,259,260,275,371,420,440,780,817,834,836,843,856,876,1149,1179]
  | 138 => [3,5,21,250,260,271,275,284,371,420,429,440,780,817,834,843,856,876,880]
  | 139 => [3,5,21,250,260,271,275,284,371,420,440,780,817,819,834,843,856,876,893]
  | 140 => [3,5,21,250,260,271,275,371,420,440,780,817,834,836,843,856,876,880,1139]
  | 142 => [3,5,21,250,260,275,283,284,371,420,429,436,440,780,817,843,856,876,884]
  | 143 => [3,5,21,250,260,275,283,284,371,420,429,440,780,817,841,843,856,876,885]
  | 144 => [3,5,21,250,260,275,283,284,371,420,436,440,780,817,819,843,856,876,895]
  | 145 => [3,5,21,250,260,275,283,284,371,420,440,780,817,819,841,843,856,876,896]
  | 146 => [3,5,21,250,260,275,283,371,420,436,440,780,817,836,843,856,876,884,1139]
  | 148 => [3,5,21,250,260,275,283,371,420,440,780,817,836,841,843,856,876,885,1139]
  | 150 => [3,5,21,250,260,275,284,371,420,429,440,780,817,834,843,856,876,884,1149]
  | 151 => [3,5,21,250,260,275,284,371,420,440,780,817,819,834,843,856,876,895,1149]
  | 152 => [3,5,21,250,260,275,371,420,440,780,817,834,836,843,856,876,884,1139,1149]
  | 154 => [3,5,21,250,260,275,371,440,442,817,843,856]
  | 155 => [3,5,21,250,260,371,420,440,780,817,843,856,1153]
  | 234 => [3,7,21,239,260,371,425,440,751,814,843,856,1153]
  | 281 => [3,8,21,34,191,260,267,275,371,416,420,440,711,746,772,780,781,821,843,856,876,1157]
  | 282 => [3,8,21,34,191,260,267,371,416,420,440,711,746,772,780,781,821,843,856,1153,1157]
  | 283 => [3,8,21,34,191,260,275,371,416,420,440,711,746,780,781,843,856,876,1146]
  | 284 => [3,8,21,34,191,260,371,416,420,440,711,746,780,781,843,856,1146,1153]
  | 344 => [3,19,21,44,170,260,371,422,425,440,665,735,751,807,843,856,1131,1153]
  | _ => []
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def src626 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,817,5,250]]
theorem sourceIDs626 : lowerHistorySourcePremises path626 = src626.map (List.map lowerHistoryBound) := by
  have hb : src626.map (List.map lowerHistoryBound) = expected626 := by
    simp only [src626, expected626, List.map_cons, List.map_nil, bound3, bound5, bound21, bound250, bound260, bound275, bound371, bound440, bound442, bound817, bound843, bound856]
  exact source626.trans hb.symm
theorem length626 : path626.alternatives = (lowerHistorySourcePremises path626).length := by
  rw [sourceIDs626]
  rfl
theorem binding626 : lowerHistoryPathBinding path626 := by
  apply BindingIds19.pathBinding_from_ids path626 src626 [] recs626 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs626 rfl records626 rfl
  · intro r hr _
    simp only [recs626, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise154)
  · intro r hr _
    simp only [recs626, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path626] using witness1123_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path626 recs626 records626 length626 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
open BindingNumeric20
theorem op125 : lowerHistoryNecessary ⟨⟨([3,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,3],[3]) = some [bv751] := by
  decide +kernel
theorem op75 : lowerHistoryPull (lowerHistoryH2) ([2,3],[3]) true = bv1131 := by
  norm_num [bv1131, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op76 : lowerHistoryNormalization ([2,3,1],[3]) true true = bv422 := by
  norm_num [bv422, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op126 : lowerHistoryNecessary ⟨⟨([3,2,3,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,3,1],[3]) = some [bv735] := by
  decide +kernel
theorem op78 : lowerHistoryNormalization ([2,3,1],[3,1]) false false = bv807 := by
  norm_num [bv807, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op127 : lowerHistoryNecessary ⟨⟨([3,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,3,1],[3,1]) = some [bv19] := by
  decide +kernel
theorem op80 : lowerHistoryNormalization ([2,3,1,1],[3,1]) false false = bv665 := by
  norm_num [bv665, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op128 : lowerHistoryNecessary ⟨⟨([3,2,3,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,3,1,1],[3,1]) = some [bv44] := by
  decide +kernel
theorem op82 : lowerHistoryPull (lowerHistoryH7) ([2,3,1,1],[3,1]) false = bv170 := by
  norm_num [bv170, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op83 : lowerHistoryPull (lowerHistoryHN) ([2,3,1,1],[3,1]) false = bv665 := by
  norm_num [bv665, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op64 : lowerHistoryNormalization ([2,3],[3,1]) false false = bv814 := by
  norm_num [bv814, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op129 : lowerHistoryNecessary ⟨⟨([3,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,3],[3,1]) = some [bv7] := by
  decide +kernel
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def path627 : LowerHistoryPath := ⟨.right,33,[3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,2,3,1,1],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩
noncomputable def raw627 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv425,bv751,bv1131,bv422,bv735,bv807,bv19,bv665,bv44,bv170,bv665]]
noncomputable def expected627 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv425,bv751,bv1131,bv422,bv735,bv807,bv19,bv665,bv44,bv170]]
theorem structural627 (ops : RootOps19.SourceOps) (b3 b19 b21 b44 b170 b260 b371 b422 b425 b440 b665 b735 b751 b807 b843 b856 b1131 b1153 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h121 : ops.relaxed ⟨([3],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h122 : ops.necessary ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h72 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = b1153)
    (h73 : ops.normalization ([2,3],[3]) true true = b425)
    (h125 : ops.necessary ⟨⟨([3,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,3],[3]) = some [b751])
    (h75 : ops.pull (lowerHistoryH2) ([2,3],[3]) true = b1131)
    (h76 : ops.normalization ([2,3,1],[3]) true true = b422)
    (h126 : ops.necessary ⟨⟨([3,2,3,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,3,1],[3]) = some [b735])
    (h78 : ops.normalization ([2,3,1],[3,1]) false false = b807)
    (h127 : ops.necessary ⟨⟨([3,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,3,1],[3,1]) = some [b19])
    (h80 : ops.normalization ([2,3,1,1],[3,1]) false false = b665)
    (h128 : ops.necessary ⟨⟨([3,2,3,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,3,1,1],[3,1]) = some [b44])
    (h82 : ops.pull (lowerHistoryH7) ([2,3,1,1],[3,1]) false = b170)
    (h83 : ops.pull (lowerHistoryHN) ([2,3,1,1],[3,1]) false = b665)
    : RootOps19.eval ops path627 = ([[b371,b843,b260,b440,b3,b856,b21,b1153,b425,b751,b1131,b422,b735,b807,b19,b665,b44,b170,b665]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,2,3,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path627, h0, h121, h2, h122, h72, h73, h125, h75, h76, h126, h78, h127, h80, h128, h82, h83, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource627 : lowerHistorySourcePremises path627 = raw627.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural627 RootOps19.actualOps bv3 bv19 bv21 bv44 bv170 bv260 bv371 bv422 bv425 bv440 bv665 bv735 bv751 bv807 bv843 bv856 bv1131 bv1153 op0 op121 op2 op122 op72 op73 op125 op75 op76 op126 op78 op127 op80 op128 op82 op83
theorem dedup627 : raw627.map List.eraseDups = expected627 := by
  decide +kernel
theorem source627 : lowerHistorySourcePremises path627 = expected627 := (rawSource627).trans (dedup627)
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def src627 : List (List Nat) := [[371,843,260,440,3,856,21,1153,425,751,1131,422,735,807,19,665,44,170]]
theorem sourceIDs627 : lowerHistorySourcePremises path627 = src627.map (List.map lowerHistoryBound) := by
  have hb : src627.map (List.map lowerHistoryBound) = expected627 := by
    simp only [src627, expected627, List.map_cons, List.map_nil, bound3, bound19, bound21, bound44, bound170, bound260, bound371, bound422, bound425, bound440, bound665, bound735, bound751, bound807, bound843, bound856, bound1131, bound1153]
  exact source627.trans hb.symm
theorem length627 : path627.alternatives = (lowerHistorySourcePremises path627).length := by
  rw [sourceIDs627]
  rfl
theorem binding627 : lowerHistoryPathBinding path627 := by
  apply BindingIds19.pathBinding_from_ids path627 src627 [] recs627 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs627 rfl records627 rfl
  · intro r hr _
    simp only [recs627, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise344)
  · intro r hr _
    simp only [recs627, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path627] using witness635_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path627 recs627 records627 length627 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
open BindingNumeric20
theorem op66 : lowerHistoryPull (lowerHistoryH7) ([2,3],[3,1]) false = bv239 := by
  norm_num [bv239, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op67 : lowerHistoryPull (lowerHistoryHN) ([2,3],[3,1]) false = bv814 := by
  norm_num [bv814, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op85 : lowerHistoryPull (lowerHistoryH9) ([2],[3]) false = bv876 := by
  norm_num [bv876, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op86 : lowerHistoryNormalization ([2,2],[3]) true true = bv420 := by
  norm_num [bv420, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op130 : lowerHistoryNecessary ⟨⟨([3,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,2],[3]) = some [bv780] := by
  decide +kernel
theorem op88 : lowerHistoryPull (lowerHistoryH2) ([2,2],[3]) true = bv1146 := by
  norm_num [bv1146, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op89 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([2,2],[3]) true = bv267 := by
  norm_num [bv267, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op90 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([2,2],[3]) true = bv821 := by
  norm_num [bv821, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op91 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([2,2],[3]) true = bv772 := by
  norm_num [bv772, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op92 : lowerHistoryPull (lowerHistoryH23) ([2,2],[3]) true = bv1157 := by
  norm_num [bv1157, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op93 : lowerHistoryNormalization ([2,2,1],[3]) true true = bv416 := by
  norm_num [bv416, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op131 : lowerHistoryNecessary ⟨⟨([3,2,2,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,2,1],[3]) = some [bv746] := by
  decide +kernel
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def path628 : LowerHistoryPath := ⟨.right,34,[3],([2],[3]),false,[(([3],[]),true),(([1],[]),true)],([3,2,3],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩
noncomputable def raw628 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv425,bv751,bv814,bv7,bv239,bv814]]
noncomputable def expected628 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv425,bv751,bv814,bv7,bv239]]
theorem structural628 (ops : RootOps19.SourceOps) (b3 b7 b21 b239 b260 b371 b425 b440 b751 b814 b843 b856 b1153 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h121 : ops.relaxed ⟨([3],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h122 : ops.necessary ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h72 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = b1153)
    (h73 : ops.normalization ([2,3],[3]) true true = b425)
    (h125 : ops.necessary ⟨⟨([3,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,3],[3]) = some [b751])
    (h64 : ops.normalization ([2,3],[3,1]) false false = b814)
    (h129 : ops.necessary ⟨⟨([3,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,3],[3,1]) = some [b7])
    (h66 : ops.pull (lowerHistoryH7) ([2,3],[3,1]) false = b239)
    (h67 : ops.pull (lowerHistoryHN) ([2,3],[3,1]) false = b814)
    : RootOps19.eval ops path628 = ([[b371,b843,b260,b440,b3,b856,b21,b1153,b425,b751,b814,b7,b239,b814]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path628, h0, h121, h2, h122, h72, h73, h125, h64, h129, h66, h67, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource628 : lowerHistorySourcePremises path628 = raw628.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural628 RootOps19.actualOps bv3 bv7 bv21 bv239 bv260 bv371 bv425 bv440 bv751 bv814 bv843 bv856 bv1153 op0 op121 op2 op122 op72 op73 op125 op64 op129 op66 op67
theorem dedup628 : raw628.map List.eraseDups = expected628 := by
  decide +kernel
theorem source628 : lowerHistorySourcePremises path628 = expected628 := (rawSource628).trans (dedup628)
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def src628 : List (List Nat) := [[371,843,260,440,3,856,21,1153,425,751,814,7,239]]
theorem sourceIDs628 : lowerHistorySourcePremises path628 = src628.map (List.map lowerHistoryBound) := by
  have hb : src628.map (List.map lowerHistoryBound) = expected628 := by
    simp only [src628, expected628, List.map_cons, List.map_nil, bound3, bound7, bound21, bound239, bound260, bound371, bound425, bound440, bound751, bound814, bound843, bound856, bound1153]
  exact source628.trans hb.symm
theorem length628 : path628.alternatives = (lowerHistorySourcePremises path628).length := by
  rw [sourceIDs628]
  rfl
theorem binding628 : lowerHistoryPathBinding path628 := by
  apply BindingIds19.pathBinding_from_ids path628 src628 [] recs628 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs628 rfl records628 rfl
  · intro r hr _
    simp only [recs628, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise234)
  · intro r hr _
    simp only [recs628, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path628] using witness767_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path628 recs628 records628 length628 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
open BindingNumeric20
theorem op95 : lowerHistoryNormalization ([2,2,1],[3,1]) false false = bv781 := by
  norm_num [bv781, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op132 : lowerHistoryNecessary ⟨⟨([3,2,2,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [bv8] := by
  decide +kernel
theorem op97 : lowerHistoryNormalization ([2,2,1,1],[3,1]) false false = bv711 := by
  norm_num [bv711, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op133 : lowerHistoryNecessary ⟨⟨([3,2,2,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,2,1,1],[3,1]) = some [bv34] := by
  decide +kernel
theorem op99 : lowerHistoryPull (lowerHistoryH7) ([2,2,1,1],[3,1]) false = bv191 := by
  norm_num [bv191, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op100 : lowerHistoryPull (lowerHistoryHN) ([2,2,1,1],[3,1]) false = bv711 := by
  norm_num [bv711, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op134 : lowerHistoryNecessary ⟨⟨([3,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,2],[3,1]) = some [bv5] := by
  decide +kernel
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def path629 : LowerHistoryPath := ⟨.right,35,[3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false)],([3,2,2,1,1],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩
noncomputable def raw629 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv420,bv780,bv1146,bv416,bv746,bv781,bv8,bv711,bv34,bv191,bv711],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv420,bv780,bv267,bv821,bv772,bv1157,bv416,bv746,bv781,bv8,bv711,bv34,bv191,bv711],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv876,bv420,bv780,bv1146,bv416,bv746,bv781,bv8,bv711,bv34,bv191,bv711],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv876,bv420,bv780,bv267,bv821,bv772,bv1157,bv416,bv746,bv781,bv8,bv711,bv34,bv191,bv711]]
noncomputable def expected629 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv420,bv780,bv1146,bv416,bv746,bv781,bv8,bv711,bv34,bv191],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv420,bv780,bv267,bv821,bv772,bv1157,bv416,bv746,bv781,bv8,bv711,bv34,bv191],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv876,bv420,bv780,bv1146,bv416,bv746,bv781,bv8,bv711,bv34,bv191],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv876,bv420,bv780,bv267,bv821,bv772,bv1157,bv416,bv746,bv781,bv8,bv711,bv34,bv191]]
theorem structural629 (ops : RootOps19.SourceOps) (b3 b8 b21 b34 b191 b260 b267 b275 b371 b416 b420 b440 b711 b746 b772 b780 b781 b821 b843 b856 b876 b1146 b1153 b1157 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h121 : ops.relaxed ⟨([3],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h122 : ops.necessary ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h72 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = b1153)
    (h62 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h85 : ops.pull (lowerHistoryH9) ([2],[3]) false = b876)
    (h86 : ops.normalization ([2,2],[3]) true true = b420)
    (h130 : ops.necessary ⟨⟨([3,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,2],[3]) = some [b780])
    (h88 : ops.pull (lowerHistoryH2) ([2,2],[3]) true = b1146)
    (h89 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,2],[3]) true = b267)
    (h90 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,2],[3]) true = b821)
    (h91 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([2,2],[3]) true = b772)
    (h92 : ops.pull (lowerHistoryH23) ([2,2],[3]) true = b1157)
    (h93 : ops.normalization ([2,2,1],[3]) true true = b416)
    (h131 : ops.necessary ⟨⟨([3,2,2,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,2,1],[3]) = some [b746])
    (h95 : ops.normalization ([2,2,1],[3,1]) false false = b781)
    (h132 : ops.necessary ⟨⟨([3,2,2,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [b8])
    (h97 : ops.normalization ([2,2,1,1],[3,1]) false false = b711)
    (h133 : ops.necessary ⟨⟨([3,2,2,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,2,1,1],[3,1]) = some [b34])
    (h99 : ops.pull (lowerHistoryH7) ([2,2,1,1],[3,1]) false = b191)
    (h100 : ops.pull (lowerHistoryHN) ([2,2,1,1],[3,1]) false = b711)
    : RootOps19.eval ops path629 = ([[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b711],[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b711],[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b711],[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b711]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,2,2,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,2,2,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path629, h0, h121, h2, h122, h72, h62, h85, h86, h130, h88, h89, h90, h91, h92, h93, h131, h95, h132, h97, h133, h99, h100, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource629 : lowerHistorySourcePremises path629 = raw629.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural629 RootOps19.actualOps bv3 bv8 bv21 bv34 bv191 bv260 bv267 bv275 bv371 bv416 bv420 bv440 bv711 bv746 bv772 bv780 bv781 bv821 bv843 bv856 bv876 bv1146 bv1153 bv1157 op0 op121 op2 op122 op72 op62 op85 op86 op130 op88 op89 op90 op91 op92 op93 op131 op95 op132 op97 op133 op99 op100
theorem dedup629 : raw629.map List.eraseDups = expected629 := by
  decide +kernel
theorem source629 : lowerHistorySourcePremises path629 = expected629 := (rawSource629).trans (dedup629)
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def src629 : List (List Nat) := [[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,191],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,191],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,191],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,191]]
theorem sourceIDs629 : lowerHistorySourcePremises path629 = src629.map (List.map lowerHistoryBound) := by
  have hb : src629.map (List.map lowerHistoryBound) = expected629 := by
    simp only [src629, expected629, List.map_cons, List.map_nil, bound3, bound8, bound21, bound34, bound191, bound260, bound267, bound275, bound371, bound416, bound420, bound440, bound711, bound746, bound772, bound780, bound781, bound821, bound843, bound856, bound876, bound1146, bound1153, bound1157]
  exact source629.trans hb.symm
theorem length629 : path629.alternatives = (lowerHistorySourcePremises path629).length := by
  rw [sourceIDs629]
  rfl
theorem binding629 : lowerHistoryPathBinding path629 := by
  apply BindingIds19.pathBinding_from_ids path629 src629 [] recs629 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs629 rfl records629 rfl
  · intro r hr _
    simp only [recs629, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise284)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise282)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise283)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise281)
  · intro r hr _
    simp only [recs629, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path629] using witness671_projection
    · simpa only [blockWids, path629] using witness671_projection
    · simpa only [blockWids, path629] using witness671_projection
    · simpa only [blockWids, path629] using witness671_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path629 recs629 records629 length629 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def path630 : LowerHistoryPath := ⟨.right,36,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),true)],([3,2,2],[3,1,3,1]),(false,false),false,2,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩
noncomputable def raw630 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv420,bv780,bv817,bv5,bv250,bv817],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv876,bv420,bv780,bv817,bv5,bv250,bv817]]
noncomputable def expected630 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv420,bv780,bv817,bv5,bv250],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv876,bv420,bv780,bv817,bv5,bv250]]
theorem structural630 (ops : RootOps19.SourceOps) (b3 b5 b21 b250 b260 b275 b371 b420 b440 b780 b817 b843 b856 b876 b1153 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h121 : ops.relaxed ⟨([3],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h122 : ops.necessary ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h72 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = b1153)
    (h62 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h85 : ops.pull (lowerHistoryH9) ([2],[3]) false = b876)
    (h86 : ops.normalization ([2,2],[3]) true true = b420)
    (h130 : ops.necessary ⟨⟨([3,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,2],[3]) = some [b780])
    (h68 : ops.normalization ([2,2],[3,1]) false false = b817)
    (h134 : ops.necessary ⟨⟨([3,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,2],[3,1]) = some [b5])
    (h70 : ops.pull (lowerHistoryH7) ([2,2],[3,1]) false = b250)
    (h71 : ops.pull (lowerHistoryHN) ([2,2],[3,1]) false = b817)
    : RootOps19.eval ops path630 = ([[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b817,b5,b250,b817],[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b817,b5,b250,b817]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path630, h0, h121, h2, h122, h72, h62, h85, h86, h130, h68, h134, h70, h71, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource630 : lowerHistorySourcePremises path630 = raw630.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural630 RootOps19.actualOps bv3 bv5 bv21 bv250 bv260 bv275 bv371 bv420 bv440 bv780 bv817 bv843 bv856 bv876 bv1153 op0 op121 op2 op122 op72 op62 op85 op86 op130 op68 op134 op70 op71
theorem dedup630 : raw630.map List.eraseDups = expected630 := by
  decide +kernel
theorem source630 : lowerHistorySourcePremises path630 = expected630 := (rawSource630).trans (dedup630)
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def extraIDs630 : List (List Nat) := [[836,1139,834,1149,884],[836,1139,834,271,880],[836,1139,283,436,884],[836,1139,283,841,885],[836,259,834,1149,1179],[836,259,834,271,1175],[836,259,283,436,1179],[836,259,283,841,1177],[284,429,834,1149,884],[284,429,834,271,880],[284,429,283,436,884],[284,429,283,841,885],[284,819,834,1149,895],[284,819,834,271,893],[284,819,283,436,895],[284,819,283,841,896]]
noncomputable def extraExpected630 : List (List CertBound) := [[bv836,bv1139,bv834,bv1149,bv884],[bv836,bv1139,bv834,bv271,bv880],[bv836,bv1139,bv283,bv436,bv884],[bv836,bv1139,bv283,bv841,bv885],[bv836,bv259,bv834,bv1149,bv1179],[bv836,bv259,bv834,bv271,bv1175],[bv836,bv259,bv283,bv436,bv1179],[bv836,bv259,bv283,bv841,bv1177],[bv284,bv429,bv834,bv1149,bv884],[bv284,bv429,bv834,bv271,bv880],[bv284,bv429,bv283,bv436,bv884],[bv284,bv429,bv283,bv841,bv885],[bv284,bv819,bv834,bv1149,bv895],[bv284,bv819,bv834,bv271,bv893],[bv284,bv819,bv283,bv436,bv895],[bv284,bv819,bv283,bv841,bv896]]
theorem extraValues630 : (List.range 16).map (BindingIds19.extras path630) = extraExpected630 := by
  decide +kernel
theorem extraIDs_sound630 : (List.range extraIDs630.length).map (BindingIds19.extras path630) = extraIDs630.map (List.map lowerHistoryBound) := by
  have hb : extraIDs630.map (List.map lowerHistoryBound) = extraExpected630 := by
    simp only [extraIDs630, extraExpected630, List.map_cons, List.map_nil, bound259, bound271, bound283, bound284, bound429, bound436, bound819, bound834, bound836, bound841, bound880, bound884, bound885, bound893, bound895, bound896, bound1139, bound1149, bound1175, bound1177, bound1179]
  exact extraValues630.trans hb.symm
end M7ContinueSep17.Noninitial20260918.B625_630

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B625_630
noncomputable def src630 : List (List Nat) := [[371,843,260,440,3,856,21,1153,420,780,817,5,250],[371,843,260,440,3,856,21,275,876,420,780,817,5,250]]
theorem sourceIDs630 : lowerHistorySourcePremises path630 = src630.map (List.map lowerHistoryBound) := by
  have hb : src630.map (List.map lowerHistoryBound) = expected630 := by
    simp only [src630, expected630, List.map_cons, List.map_nil, bound3, bound5, bound21, bound250, bound260, bound275, bound371, bound420, bound440, bound780, bound817, bound843, bound856, bound876, bound1153]
  exact source630.trans hb.symm
theorem length630 : path630.alternatives = (lowerHistorySourcePremises path630).length := by
  rw [sourceIDs630]
  rfl
theorem binding630 : lowerHistoryPathBinding path630 := by
  apply BindingIds19.pathBinding_from_ids path630 src630 extraIDs630 recs630 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs630 extraIDs_sound630 records630 rfl
  · intro r hr _
    simp only [recs630, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise155)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise152)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise140)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise146)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise148)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise137)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise134)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise135)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise136)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise150)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise138)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise142)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise143)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise151)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise139)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise144)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise145)
  · intro r hr _
    simp only [recs630, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path630] using witness1045_projection
    · simpa only [blockWids, path630] using witness1017_projection
    · simpa only [blockWids, path630] using witness1017_projection
    · simpa only [blockWids, path630] using witness541_projection
    · simpa only [blockWids, path630] using witness1017_projection
    · simpa only [blockWids, path630] using witness1033_projection
    · simpa only [blockWids, path630] using witness791_projection
    · simpa only [blockWids, path630] using witness527_projection
    · simpa only [blockWids, path630] using witness791_projection
    · simpa only [blockWids, path630] using witness319_projection
    · simpa only [blockWids, path630] using witness299_projection
    · simpa only [blockWids, path630] using witness531_projection
    · simpa only [blockWids, path630] using witness307_projection
    · simpa only [blockWids, path630] using witness1033_projection
    · simpa only [blockWids, path630] using witness800_projection
    · simpa only [blockWids, path630] using witness535_projection
    · simpa only [blockWids, path630] using witness804_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path630 recs630 records630 length630 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B625_630

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
namespace M7ContinueSep17.Noninitial20260918.B625_630
theorem _root_.solution : lowerHistoryBindingBatch 625 630 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[625]? = some M7ContinueSep17.Noninitial20260918.B625_630.path626 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 31 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding626
  · have hl : lowerHistoryPaths[626]? = some M7ContinueSep17.Noninitial20260918.B625_630.path627 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 32 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding627
  · have hl : lowerHistoryPaths[627]? = some M7ContinueSep17.Noninitial20260918.B625_630.path628 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 33 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding628
  · have hl : lowerHistoryPaths[628]? = some M7ContinueSep17.Noninitial20260918.B625_630.path629 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 34 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding629
  · have hl : lowerHistoryPaths[629]? = some M7ContinueSep17.Noninitial20260918.B625_630.path630 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupR 35 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding630
end M7ContinueSep17.Noninitial20260918.B625_630

#print axioms solution
