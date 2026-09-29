-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1070_1075
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T05:17:01.867057+00:00
-- url     : https://prove2.me/submissions/169f8c38-1516-4338-9d35-d6989bbf7b96

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
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def bv1 : CertBound := ⟨true,false,⟨⟨(-5134/1081),(3851/1081),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩⟩⟩
noncomputable def bv5 : CertBound := ⟨true,false,⟨⟨(-4078497/4976303),(3063403/4976303),(0),(0)⟩,⟨(168/409),(1/409),(0),(0)⟩,⟨(223/529),(-1/529),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv7 : CertBound := ⟨true,false,⟨⟨(-2415463/5270749),(1816717/5270749),(0),(0)⟩,⟨(109/251),(1/753),(0),(0)⟩,⟨(402/913),(-1/913),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv8 : CertBound := ⟨true,false,⟨⟨(-1707521/5116787),(1276674/5116787),(0),(0)⟩,⟨(594/1417),(1/1417),(0),(0)⟩,⟨(133/314),(-1/942),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv19 : CertBound := ⟨true,false,⟨⟨(-2957543/15273863),(2209052/15273863),(0),(0)⟩,⟨(363/827),(1/2481),(0),(0)⟩,⟨(709/1606),(-1/1606),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩⟩⟩
noncomputable def bv238 : CertBound := ⟨true,false,⟨⟨(10372299021/84769894000),(-28232289/84769894000),(0),(0)⟩,⟨(31755/72022),(1/72022),(0),(0)⟩,⟨(709/1606),(-1/1606),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩⟩⟩
noncomputable def bv247 : CertBound := ⟨true,false,⟨⟨(147606791679/705524402000),(67518837/705524402000),(0),(0)⟩,⟨(17749/41998),(1/41998),(0),(0)⟩,⟨(133/314),(-1/942),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩⟩⟩
noncomputable def bv260 : CertBound := ⟨true,false,⟨⟨(31/100),(0),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv275 : CertBound := ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv293 : CertBound := ⟨true,false,⟨⟨(3/2),(0),(0),(1/10)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv296 : CertBound := ⟨true,false,⟨⟨(930648861/322391000),(11126241/322391000),(0),(0)⟩,⟨(1272/3013),(1/3013),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv422 : CertBound := ⟨true,true,⟨⟨(5/17),(0),(0),(-4/85)⟩,⟨(73/170),(0),(0),(1/510)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv425 : CertBound := ⟨true,true,⟨⟨(363/1010),(0),(0),(-37/1010)⟩,⟨(83/202),(0),(0),(1/202)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),(0),(0)⟩,⟨(-1/2),(1/2),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv442 : CertBound := ⟨true,true,⟨⟨(3317/299),(-1683/299),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(1),(-1/3),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv735 : CertBound := ⟨false,false,⟨⟨(215681/1863433),(162441/1863433),(0),(0)⟩,⟨(402/913),(-1/913),(0),(0)⟩,⟨(761/1727),(1/5181),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv751 : CertBound := ⟨false,false,⟨⟨(356680/2447159),(867844/2447159),(0),(0)⟩,⟨(761/1727),(1/5181),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv766 : CertBound := ⟨false,false,⟨⟨(1208864407/7105666700),(-9395003/10658500050),(0),(0)⟩,⟨(363/827),(1/2481),(0),(0)⟩,⟨(709/1606),(-1/1606),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv781 : CertBound := ⟨false,false,⟨⟨(1167/4454),(0),(0),(71/4454)⟩,⟨(105/262),(0),(0),(1/262)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv791 : CertBound := ⟨false,false,⟨⟨(51076124637/173770535900),(-155623369/130327901925),(0),(0)⟩,⟨(594/1417),(1/1417),(0),(0)⟩,⟨(133/314),(-1/942),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv807 : CertBound := ⟨false,false,⟨⟨(13/34),(0),(0),(-7/170)⟩,⟨(73/170),(0),(0),(1/510)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv814 : CertBound := ⟨false,false,⟨⟨(537/1010),(0),(0),(-13/1010)⟩,⟨(83/202),(0),(0),(1/202)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv817 : CertBound := ⟨false,false,⟨⟨(753/1394),(0),(0),(91/1394)⟩,⟨(29/82),(0),(0),(1/82)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv856 : CertBound := ⟨false,false,⟨⟨(3/2),(0),(0),(1/10)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv857 : CertBound := ⟨false,false,⟨⟨(10485/6253),(24757/6253),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv867 : CertBound := ⟨false,false,⟨⟨(3),(0),(0),(2/5)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv871 : CertBound := ⟨false,false,⟨⟨(890072666/211092275),(-5511187/2533107300),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(1950/7081),(-1/7081),(0),(0)⟩,⟨(767/2749),(1/2749),(0),(0)⟩⟩⟩
noncomputable def bv1131 : CertBound := ⟨false,true,⟨⟨(28448350/118788241),(9050/118788241),(0),(0)⟩,⟨(6265/14278),(-1/14278),(0),(0)⟩,⟨(761/1727),(1/5181),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1153 : CertBound := ⟨false,true,⟨⟨(3087972/5986825),(290501/2394730),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [bv371,bv843,bv260,bv440] := by
  simpa only [bv371,bv843,bv260,bv440] using BindingNumeric20.initial_base
theorem op44 : lowerHistoryRelaxedGoodness ⟨([3,1,3],[3,1]),(false,false)⟩ = some [bv3] := by
  decide +kernel
theorem op37 : lowerHistoryNormalization ([2],[3]) true false = bv293 := by
  norm_num [bv293, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op106 : lowerHistoryNecessary ⟨⟨([3,1,3,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([2],[3]) = some [bv857] := by
  decide +kernel
theorem op39 : lowerHistoryNormalization ([2],[3,1]) false false = bv867 := by
  norm_num [bv867, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op107 : lowerHistoryNecessary ⟨⟨([3,1,3,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[3,1]) = some [bv1] := by
  decide +kernel
theorem op41 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2],[3,1]) false = bv871 := by
  norm_num [bv871, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op42 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2],[3,1]) false = bv296 := by
  norm_num [bv296, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op43 : lowerHistoryPull (lowerHistoryHN) ([2],[3,1]) false = bv867 := by
  norm_num [bv867, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op108 : lowerHistoryRelaxedGoodness ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [bv3] := by
  decide +kernel
theorem op2 : lowerHistoryNormalization ([2],[3]) false false = bv856 := by
  norm_num [bv856, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op109 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [bv21] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def path1071 : LowerHistoryPath := ⟨.rightMixed,75,[3,1,3],([2],[3]),true,[(([1],[]),true)],([3,1,3,2],[3,1,3,1]),(true,false),false,4,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩
noncomputable def raw1071 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv293,bv857,bv867,bv1,bv871,bv296,bv867]]
noncomputable def expected1071 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv293,bv857,bv867,bv1,bv871,bv296]]
theorem structural1071 (ops : RootOps19.SourceOps) (b1 b3 b260 b293 b296 b371 b440 b843 b857 b867 b871 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h44 : ops.relaxed ⟨([3,1,3],[3,1]),(false,false)⟩ = some [b3])
    (h37 : ops.normalization ([2],[3]) true false = b293)
    (h106 : ops.necessary ⟨⟨([3,1,3,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([2],[3]) = some [b857])
    (h39 : ops.normalization ([2],[3,1]) false false = b867)
    (h107 : ops.necessary ⟨⟨([3,1,3,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[3,1]) = some [b1])
    (h41 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2],[3,1]) false = b871)
    (h42 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2],[3,1]) false = b296)
    (h43 : ops.pull (lowerHistoryHN) ([2],[3,1]) false = b867)
    : RootOps19.eval ops path1071 = ([[b371,b843,b260,b440,b3,b293,b857,b867,b1,b871,b296,b867]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1071, h0, h44, h37, h106, h39, h107, h41, h42, h43, hc0, hf0, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1071 : lowerHistorySourcePremises path1071 = raw1071.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1071 RootOps19.actualOps bv1 bv3 bv260 bv293 bv296 bv371 bv440 bv843 bv857 bv867 bv871 op0 op44 op37 op106 op39 op107 op41 op42 op43
theorem dedup1071 : raw1071.map List.eraseDups = expected1071 := by
  decide +kernel
theorem source1071 : lowerHistorySourcePremises path1071 = expected1071 := (rawSource1071).trans (dedup1071)
end M7ContinueSep17.Initial20260918.B1070_1075

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
namespace M7ContinueSep17.Initial20260918.B1070_1075
theorem bound1 : lowerHistoryBound 1 = bv1 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[0]? = some bv1 := Eq.refl (some bv1)
  exact (BoundCompact16.global_to_chunk1 0 (by decide)).trans hl
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
theorem bound238 : lowerHistoryBound 238 = bv238 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[37]? = some bv238 := Eq.refl (some bv238)
  exact (BoundCompact16.global_to_chunk2 37 (by decide)).trans hl
theorem bound247 : lowerHistoryBound 247 = bv247 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[46]? = some bv247 := Eq.refl (some bv247)
  exact (BoundCompact16.global_to_chunk2 46 (by decide)).trans hl
theorem bound260 : lowerHistoryBound 260 = bv260 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[59]? = some bv260 := Eq.refl (some bv260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hl
theorem bound275 : lowerHistoryBound 275 = bv275 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[74]? = some bv275 := Eq.refl (some bv275)
  exact (BoundCompact16.global_to_chunk2 74 (by decide)).trans hl
theorem bound293 : lowerHistoryBound 293 = bv293 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[92]? = some bv293 := Eq.refl (some bv293)
  exact (BoundCompact16.global_to_chunk2 92 (by decide)).trans hl
theorem bound296 : lowerHistoryBound 296 = bv296 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[95]? = some bv296 := Eq.refl (some bv296)
  exact (BoundCompact16.global_to_chunk2 95 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound422 : lowerHistoryBound 422 = bv422 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[21]? = some bv422 := Eq.refl (some bv422)
  exact (BoundCompact16.global_to_chunk3 21 (by decide)).trans hl
theorem bound425 : lowerHistoryBound 425 = bv425 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[24]? = some bv425 := Eq.refl (some bv425)
  exact (BoundCompact16.global_to_chunk3 24 (by decide)).trans hl
theorem bound440 : lowerHistoryBound 440 = bv440 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[39]? = some bv440 := Eq.refl (some bv440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hl
theorem bound442 : lowerHistoryBound 442 = bv442 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[41]? = some bv442 := Eq.refl (some bv442)
  exact (BoundCompact16.global_to_chunk3 41 (by decide)).trans hl
theorem bound735 : lowerHistoryBound 735 = bv735 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[134]? = some bv735 := Eq.refl (some bv735)
  exact (BoundCompact16.global_to_chunk4 134 (by decide)).trans hl
theorem bound751 : lowerHistoryBound 751 = bv751 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[150]? = some bv751 := Eq.refl (some bv751)
  exact (BoundCompact16.global_to_chunk4 150 (by decide)).trans hl
theorem bound766 : lowerHistoryBound 766 = bv766 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[165]? = some bv766 := Eq.refl (some bv766)
  exact (BoundCompact16.global_to_chunk4 165 (by decide)).trans hl
theorem bound781 : lowerHistoryBound 781 = bv781 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[180]? = some bv781 := Eq.refl (some bv781)
  exact (BoundCompact16.global_to_chunk4 180 (by decide)).trans hl
theorem bound791 : lowerHistoryBound 791 = bv791 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[190]? = some bv791 := Eq.refl (some bv791)
  exact (BoundCompact16.global_to_chunk4 190 (by decide)).trans hl
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
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound856 : lowerHistoryBound 856 = bv856 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[55]? = some bv856 := Eq.refl (some bv856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hl
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
theorem bound1131 : lowerHistoryBound 1131 = bv1131 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[130]? = some bv1131 := Eq.refl (some bv1131)
  exact (BoundCompact16.global_to_chunk6 130).trans hl
theorem bound1153 : lowerHistoryBound 1153 = bv1153 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[152]? = some bv1153 := Eq.refl (some bv1153)
  exact (BoundCompact16.global_to_chunk6 152).trans hl
end M7ContinueSep17.Initial20260918.B1070_1075

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
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def recs1071 : List LowerHistoryRecord := [⟨.rightMixed,75,0,(-1),false,16,282⟩]
theorem records1071 : lowerHistoryRecordsFor (⟨.rightMixed,75,[3,1,3],([2],[3]),true,[(([1],[]),true)],([3,1,3,2],[3,1,3,1]),(true,false),false,4,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1071 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 75)) = recs1071
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
noncomputable def recs1072 : List LowerHistoryRecord := [⟨.rightMixed,76,0,(-1),false,211,1092⟩]
theorem records1072 : lowerHistoryRecordsFor (⟨.rightMixed,76,[3,1,3,1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false)],([3,1,3,1,2,3,1],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1072 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 76)) = recs1072
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
noncomputable def recs1073 : List LowerHistoryRecord := [⟨.rightMixed,77,0,(-1),false,102,1104⟩]
theorem records1073 : lowerHistoryRecordsFor (⟨.rightMixed,77,[3,1,3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false)],([3,1,3,1,2,2,1],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1073 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 77)) = recs1073
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
noncomputable def recs1074 : List LowerHistoryRecord := [⟨.rightMixed,78,0,(-1),false,347,712⟩]
theorem records1074 : lowerHistoryRecordsFor (⟨.rightMixed,78,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true)],([3,1,3,1,2,3,1],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1074 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 78)) = recs1074
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
noncomputable def recs1075 : List LowerHistoryRecord := [⟨.rightMixed,79,0,(-1),false,212,712⟩]
theorem records1075 : lowerHistoryRecordsFor (⟨.rightMixed,79,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false)],([3,1,3,1,2,3,1],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs1075 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .rightMixed).filter (fun r => decide (r.catalog = .rightMixed ∧ r.pathId = 79)) = recs1075
  rw [M7ContinueSep17.CatalogueGeneral.catalogListX]
  rfl
end M7ContinueSep17.Initial20260918.B1070_1075

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
namespace M7ContinueSep17.Initial20260918.B1070_1075
theorem premise16 : lowerHistoryPremises[15]? = some ([1,3,260,293,296,371,440,843,857,867,871] : List Nat) := by
  have hg : lowerHistoryPremises[15]? = lowerHistoryPremises01[15]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 15 (by decide)
  exact hg.trans (by rfl)
theorem premise102 : lowerHistoryPremises[101]? = some ([3,5,8,21,247,260,275,371,440,442,781,791,817,843,856] : List Nat) := by
  have hg : lowerHistoryPremises[101]? = lowerHistoryPremises01[101]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 101 (by decide)
  exact hg.trans (by rfl)
theorem premise211 : lowerHistoryPremises[210]? = some ([3,7,19,21,238,260,275,371,440,442,766,807,814,843,856] : List Nat) := by
  have hg : lowerHistoryPremises[210]? = lowerHistoryPremises02[10]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 10 (by decide)
  exact hg.trans (by rfl)
theorem premise212 : lowerHistoryPremises[211]? = some ([3,7,19,21,238,260,371,425,440,751,766,807,814,843,856,1153] : List Nat) := by
  have hg : lowerHistoryPremises[211]? = lowerHistoryPremises02[11]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 11 (by decide)
  exact hg.trans (by rfl)
theorem premise347 : lowerHistoryPremises[346]? = some ([3,19,21,238,260,371,422,425,440,735,751,766,807,843,856,1131,1153] : List Nat) := by
  have hg : lowerHistoryPremises[346]? = lowerHistoryPremises02[146]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 146 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1070_1075
theorem witness282_projection : (lowerHistoryWitness 282).lowerBound = lowerHistoryBound 296 ∧ (lowerHistoryWitness 282).upperBound = lowerHistoryBound 843 ∧ (lowerHistoryWitness 282).rectangle = (⟨(5/19),(4/15),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[81]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 296, lowerHistoryBound 843, (⟨(5/19),(4/15),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 296, lowerHistoryBound 843, (⟨(5/19),(4/15),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[281]? = lowerHistoryWitnesses02[81]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 81 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness712_projection : (lowerHistoryWitness 712).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 712).upperBound = lowerHistoryBound 766 ∧ (lowerHistoryWitness 712).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[111]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 766, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 766, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[711]? = lowerHistoryWitnesses04[111]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 111 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1092_projection : (lowerHistoryWitness 1092).lowerBound = lowerHistoryBound 442 ∧ (lowerHistoryWitness 1092).upperBound = lowerHistoryBound 766 ∧ (lowerHistoryWitness 1092).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[91]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 766, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 766, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1091]? = lowerHistoryWitnesses06[91]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 91 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness1104_projection : (lowerHistoryWitness 1104).lowerBound = lowerHistoryBound 442 ∧ (lowerHistoryWitness 1104).upperBound = lowerHistoryBound 791 ∧ (lowerHistoryWitness 1104).rectangle = (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[103]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 791, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 791, (⟨(15/19),(19/24),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[1103]? = lowerHistoryWitnesses06[103]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk6 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 103 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 282 => (296,843)
  | 712 => (440,766)
  | 1092 => (442,766)
  | 1104 => (442,791)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 16 => [1,3,260,293,296,371,440,843,857,867,871]
  | 102 => [3,5,8,21,247,260,275,371,440,442,781,791,817,843,856]
  | 211 => [3,7,19,21,238,260,275,371,440,442,766,807,814,843,856]
  | 212 => [3,7,19,21,238,260,371,425,440,751,766,807,814,843,856,1153]
  | 347 => [3,19,21,238,260,371,422,425,440,735,751,766,807,843,856,1131,1153]
  | _ => []
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def src1071 : List (List Nat) := [[371,843,260,440,3,293,857,867,1,871,296]]
theorem sourceIDs1071 : lowerHistorySourcePremises path1071 = src1071.map (List.map lowerHistoryBound) := by
  have hb : src1071.map (List.map lowerHistoryBound) = expected1071 := by
    simp only [src1071, expected1071, List.map_cons, List.map_nil, bound1, bound3, bound260, bound293, bound296, bound371, bound440, bound843, bound857, bound867, bound871]
  exact source1071.trans hb.symm
theorem length1071 : path1071.alternatives = (lowerHistorySourcePremises path1071).length := by
  rw [sourceIDs1071]
  rfl
theorem binding1071 : lowerHistoryPathBinding path1071 := by
  apply BindingIds19.pathBinding_from_ids path1071 src1071 [] recs1071 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1071 rfl records1071 rfl
  · intro r hr _
    simp only [recs1071, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise16)
  · intro r hr _
    simp only [recs1071, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1071] using witness282_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1071 recs1071 records1071 length1071 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
open BindingNumeric20
theorem op46 : lowerHistoryPull (lowerHistoryH7) ([2],[3]) false = bv275 := by
  norm_num [bv275, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op47 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = bv442 := by
  norm_num [bv442, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op48 : lowerHistoryNormalization ([2,3],[3,1]) false false = bv814 := by
  norm_num [bv814, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op110 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [bv7] := by
  decide +kernel
theorem op50 : lowerHistoryNormalization ([2,3,1],[3,1]) false false = bv807 := by
  norm_num [bv807, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op111 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,3,1],[3,1]) = some [bv19] := by
  decide +kernel
theorem op52 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) false = bv766 := by
  norm_num [bv766, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op53 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,3,1],[3,1]) false = bv238 := by
  norm_num [bv238, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op54 : lowerHistoryPull (lowerHistoryHN) ([2,3,1],[3,1]) false = bv807 := by
  norm_num [bv807, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op55 : lowerHistoryNormalization ([2,2],[3,1]) false false = bv817 := by
  norm_num [bv817, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op112 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [bv5] := by
  decide +kernel
theorem op57 : lowerHistoryNormalization ([2,2,1],[3,1]) false false = bv781 := by
  norm_num [bv781, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def path1072 : LowerHistoryPath := ⟨.rightMixed,76,[3,1,3,1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false)],([3,1,3,1,2,3,1],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩
noncomputable def raw1072 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv814,bv7,bv807,bv19,bv766,bv238,bv807]]
noncomputable def expected1072 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv814,bv7,bv807,bv19,bv766,bv238]]
theorem structural1072 (ops : RootOps19.SourceOps) (b3 b7 b19 b21 b238 b260 b275 b371 b440 b442 b766 b807 b814 b843 b856 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h108 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h109 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h46 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h47 : ops.pull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = b442)
    (h48 : ops.normalization ([2,3],[3,1]) false false = b814)
    (h110 : ops.necessary ⟨⟨([3,1,3,1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [b7])
    (h50 : ops.normalization ([2,3,1],[3,1]) false false = b807)
    (h111 : ops.necessary ⟨⟨([3,1,3,1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,3,1],[3,1]) = some [b19])
    (h52 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) false = b766)
    (h53 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,3,1],[3,1]) false = b238)
    (h54 : ops.pull (lowerHistoryHN) ([2,3,1],[3,1]) false = b807)
    : RootOps19.eval ops path1072 = ([[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b807,b19,b766,b238,b807]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,(lowerHistoryComplement lowerHistoryH9)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([3],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1072, h0, h108, h2, h109, h46, h47, h48, h110, h50, h111, h52, h53, h54, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1072 : lowerHistorySourcePremises path1072 = raw1072.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1072 RootOps19.actualOps bv3 bv7 bv19 bv21 bv238 bv260 bv275 bv371 bv440 bv442 bv766 bv807 bv814 bv843 bv856 op0 op108 op2 op109 op46 op47 op48 op110 op50 op111 op52 op53 op54
theorem dedup1072 : raw1072.map List.eraseDups = expected1072 := by
  decide +kernel
theorem source1072 : lowerHistorySourcePremises path1072 = expected1072 := (rawSource1072).trans (dedup1072)
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def src1072 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,814,7,807,19,766,238]]
theorem sourceIDs1072 : lowerHistorySourcePremises path1072 = src1072.map (List.map lowerHistoryBound) := by
  have hb : src1072.map (List.map lowerHistoryBound) = expected1072 := by
    simp only [src1072, expected1072, List.map_cons, List.map_nil, bound3, bound7, bound19, bound21, bound238, bound260, bound275, bound371, bound440, bound442, bound766, bound807, bound814, bound843, bound856]
  exact source1072.trans hb.symm
theorem length1072 : path1072.alternatives = (lowerHistorySourcePremises path1072).length := by
  rw [sourceIDs1072]
  rfl
theorem binding1072 : lowerHistoryPathBinding path1072 := by
  apply BindingIds19.pathBinding_from_ids path1072 src1072 [] recs1072 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1072 rfl records1072 rfl
  · intro r hr _
    simp only [recs1072, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise211)
  · intro r hr _
    simp only [recs1072, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1072] using witness1092_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1072 recs1072 records1072 length1072 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
open BindingNumeric20
theorem op113 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,2,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,2,1],[3,1]) = some [bv8] := by
  decide +kernel
theorem op59 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,2,1],[3,1]) false = bv791 := by
  norm_num [bv791, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op60 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,2,1],[3,1]) false = bv247 := by
  norm_num [bv247, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op61 : lowerHistoryPull (lowerHistoryHN) ([2,2,1],[3,1]) false = bv781 := by
  norm_num [bv781, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op62 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = bv1153 := by
  norm_num [bv1153, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op63 : lowerHistoryNormalization ([2,3],[3]) true true = bv425 := by
  norm_num [bv425, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op114 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,3],[3]) = some [bv751] := by
  decide +kernel
theorem op65 : lowerHistoryPull (lowerHistoryH2) ([2,3],[3]) true = bv1131 := by
  norm_num [bv1131, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op66 : lowerHistoryNormalization ([2,3,1],[3]) true true = bv422 := by
  norm_num [bv422, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op115 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,3,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,3,1],[3]) = some [bv735] := by
  decide +kernel
theorem op116 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,3,1],[3,1]) = some [bv19] := by
  decide +kernel
theorem op117 : lowerHistoryNecessary ⟨⟨([3,1,3,1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,3],[3,1]) = some [bv7] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def path1073 : LowerHistoryPath := ⟨.rightMixed,77,[3,1,3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false)],([3,1,3,1,2,2,1],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩
noncomputable def raw1073 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv781,bv8,bv791,bv247,bv781]]
noncomputable def expected1073 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv442,bv817,bv5,bv781,bv8,bv791,bv247]]
theorem structural1073 (ops : RootOps19.SourceOps) (b3 b5 b8 b21 b247 b260 b275 b371 b440 b442 b781 b791 b817 b843 b856 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h108 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h109 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h46 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h47 : ops.pull ((lowerHistoryComplement lowerHistoryH9)) ([2],[3]) false = b442)
    (h55 : ops.normalization ([2,2],[3,1]) false false = b817)
    (h112 : ops.necessary ⟨⟨([3,1,3,1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [b5])
    (h57 : ops.normalization ([2,2,1],[3,1]) false false = b781)
    (h113 : ops.necessary ⟨⟨([3,1,3,1,2,2,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,2,1],[3,1]) = some [b8])
    (h59 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,2,1],[3,1]) false = b791)
    (h60 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,2,1],[3,1]) false = b247)
    (h61 : ops.pull (lowerHistoryHN) ([2,2,1],[3,1]) false = b781)
    : RootOps19.eval ops path1073 = ([[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b781,b8,b791,b247,b781]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[1]) = [[lowerHistoryH7,(lowerHistoryComplement lowerHistoryH9)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1073, h0, h108, h2, h109, h46, h47, h55, h112, h57, h113, h59, h60, h61, hc0, hc1, hf0, hf1, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1073 : lowerHistorySourcePremises path1073 = raw1073.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1073 RootOps19.actualOps bv3 bv5 bv8 bv21 bv247 bv260 bv275 bv371 bv440 bv442 bv781 bv791 bv817 bv843 bv856 op0 op108 op2 op109 op46 op47 op55 op112 op57 op113 op59 op60 op61
theorem dedup1073 : raw1073.map List.eraseDups = expected1073 := by
  decide +kernel
theorem source1073 : lowerHistorySourcePremises path1073 = expected1073 := (rawSource1073).trans (dedup1073)
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def src1073 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,817,5,781,8,791,247]]
theorem sourceIDs1073 : lowerHistorySourcePremises path1073 = src1073.map (List.map lowerHistoryBound) := by
  have hb : src1073.map (List.map lowerHistoryBound) = expected1073 := by
    simp only [src1073, expected1073, List.map_cons, List.map_nil, bound3, bound5, bound8, bound21, bound247, bound260, bound275, bound371, bound440, bound442, bound781, bound791, bound817, bound843, bound856]
  exact source1073.trans hb.symm
theorem length1073 : path1073.alternatives = (lowerHistorySourcePremises path1073).length := by
  rw [sourceIDs1073]
  rfl
theorem binding1073 : lowerHistoryPathBinding path1073 := by
  apply BindingIds19.pathBinding_from_ids path1073 src1073 [] recs1073 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1073 rfl records1073 rfl
  · intro r hr _
    simp only [recs1073, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise102)
  · intro r hr _
    simp only [recs1073, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1073] using witness1104_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1073 recs1073 records1073 length1073 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def path1074 : LowerHistoryPath := ⟨.rightMixed,78,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true)],([3,1,3,1,2,3,1],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩
noncomputable def raw1074 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv425,bv751,bv1131,bv422,bv735,bv807,bv19,bv766,bv238,bv807]]
noncomputable def expected1074 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv425,bv751,bv1131,bv422,bv735,bv807,bv19,bv766,bv238]]
theorem structural1074 (ops : RootOps19.SourceOps) (b3 b19 b21 b238 b260 b371 b422 b425 b440 b735 b751 b766 b807 b843 b856 b1131 b1153 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h108 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h109 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h62 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = b1153)
    (h63 : ops.normalization ([2,3],[3]) true true = b425)
    (h114 : ops.necessary ⟨⟨([3,1,3,1,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,3],[3]) = some [b751])
    (h65 : ops.pull (lowerHistoryH2) ([2,3],[3]) true = b1131)
    (h66 : ops.normalization ([2,3,1],[3]) true true = b422)
    (h115 : ops.necessary ⟨⟨([3,1,3,1,2,3,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,3,1],[3]) = some [b735])
    (h50 : ops.normalization ([2,3,1],[3,1]) false false = b807)
    (h116 : ops.necessary ⟨⟨([3,1,3,1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,3,1],[3,1]) = some [b19])
    (h52 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) false = b766)
    (h53 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,3,1],[3,1]) false = b238)
    (h54 : ops.pull (lowerHistoryHN) ([2,3,1],[3,1]) false = b807)
    : RootOps19.eval ops path1074 = ([[b371,b843,b260,b440,b3,b856,b21,b1153,b425,b751,b1131,b422,b735,b807,b19,b766,b238,b807]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,3,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1074, h0, h108, h2, h109, h62, h63, h114, h65, h66, h115, h50, h116, h52, h53, h54, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1074 : lowerHistorySourcePremises path1074 = raw1074.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1074 RootOps19.actualOps bv3 bv19 bv21 bv238 bv260 bv371 bv422 bv425 bv440 bv735 bv751 bv766 bv807 bv843 bv856 bv1131 bv1153 op0 op108 op2 op109 op62 op63 op114 op65 op66 op115 op50 op116 op52 op53 op54
theorem dedup1074 : raw1074.map List.eraseDups = expected1074 := by
  decide +kernel
theorem source1074 : lowerHistorySourcePremises path1074 = expected1074 := (rawSource1074).trans (dedup1074)
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def src1074 : List (List Nat) := [[371,843,260,440,3,856,21,1153,425,751,1131,422,735,807,19,766,238]]
theorem sourceIDs1074 : lowerHistorySourcePremises path1074 = src1074.map (List.map lowerHistoryBound) := by
  have hb : src1074.map (List.map lowerHistoryBound) = expected1074 := by
    simp only [src1074, expected1074, List.map_cons, List.map_nil, bound3, bound19, bound21, bound238, bound260, bound371, bound422, bound425, bound440, bound735, bound751, bound766, bound807, bound843, bound856, bound1131, bound1153]
  exact source1074.trans hb.symm
theorem length1074 : path1074.alternatives = (lowerHistorySourcePremises path1074).length := by
  rw [sourceIDs1074]
  rfl
theorem binding1074 : lowerHistoryPathBinding path1074 := by
  apply BindingIds19.pathBinding_from_ids path1074 src1074 [] recs1074 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1074 rfl records1074 rfl
  · intro r hr _
    simp only [recs1074, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise347)
  · intro r hr _
    simp only [recs1074, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1074] using witness712_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1074 recs1074 records1074 length1074 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def path1075 : LowerHistoryPath := ⟨.rightMixed,79,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false)],([3,1,3,1,2,3,1],[3,1,3,1]),(true,false),false,4,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩
noncomputable def raw1075 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv425,bv751,bv814,bv7,bv807,bv19,bv766,bv238,bv807]]
noncomputable def expected1075 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv425,bv751,bv814,bv7,bv807,bv19,bv766,bv238]]
theorem structural1075 (ops : RootOps19.SourceOps) (b3 b7 b19 b21 b238 b260 b371 b425 b440 b751 b766 b807 b814 b843 b856 b1153 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h108 : ops.relaxed ⟨([3,1,3,1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h109 : ops.necessary ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h62 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = b1153)
    (h63 : ops.normalization ([2,3],[3]) true true = b425)
    (h114 : ops.necessary ⟨⟨([3,1,3,1,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,3],[3]) = some [b751])
    (h48 : ops.normalization ([2,3],[3,1]) false false = b814)
    (h117 : ops.necessary ⟨⟨([3,1,3,1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,3],[3,1]) = some [b7])
    (h50 : ops.normalization ([2,3,1],[3,1]) false false = b807)
    (h111 : ops.necessary ⟨⟨([3,1,3,1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,3,1],[3,1]) = some [b19])
    (h52 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) false = b766)
    (h53 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,3,1],[3,1]) false = b238)
    (h54 : ops.pull (lowerHistoryHN) ([2,3,1],[3,1]) false = b807)
    : RootOps19.eval ops path1075 = ([[b371,b843,b260,b440,b3,b856,b21,b1153,b425,b751,b814,b7,b807,b19,b766,b238,b807]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,3],[3,1,3]),(false,true)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,3,1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1075, h0, h108, h2, h109, h62, h63, h114, h48, h117, h50, h111, h52, h53, h54, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1075 : lowerHistorySourcePremises path1075 = raw1075.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1075 RootOps19.actualOps bv3 bv7 bv19 bv21 bv238 bv260 bv371 bv425 bv440 bv751 bv766 bv807 bv814 bv843 bv856 bv1153 op0 op108 op2 op109 op62 op63 op114 op48 op117 op50 op111 op52 op53 op54
theorem dedup1075 : raw1075.map List.eraseDups = expected1075 := by
  decide +kernel
theorem source1075 : lowerHistorySourcePremises path1075 = expected1075 := (rawSource1075).trans (dedup1075)
end M7ContinueSep17.Initial20260918.B1070_1075

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1070_1075
noncomputable def src1075 : List (List Nat) := [[371,843,260,440,3,856,21,1153,425,751,814,7,807,19,766,238]]
theorem sourceIDs1075 : lowerHistorySourcePremises path1075 = src1075.map (List.map lowerHistoryBound) := by
  have hb : src1075.map (List.map lowerHistoryBound) = expected1075 := by
    simp only [src1075, expected1075, List.map_cons, List.map_nil, bound3, bound7, bound19, bound21, bound238, bound260, bound371, bound425, bound440, bound751, bound766, bound807, bound814, bound843, bound856, bound1153]
  exact source1075.trans hb.symm
theorem length1075 : path1075.alternatives = (lowerHistorySourcePremises path1075).length := by
  rw [sourceIDs1075]
  rfl
theorem binding1075 : lowerHistoryPathBinding path1075 := by
  apply BindingIds19.pathBinding_from_ids path1075 src1075 [] recs1075 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1075 rfl records1075 rfl
  · intro r hr _
    simp only [recs1075, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise212)
  · intro r hr _
    simp only [recs1075, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1075] using witness712_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1075 recs1075 records1075 length1075 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1070_1075

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
namespace M7ContinueSep17.Initial20260918.B1070_1075
theorem _root_.solution : lowerHistoryBindingBatch 1070 1075 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1070]? = some M7ContinueSep17.Initial20260918.B1070_1075.path1071 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 74 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1071
  · have hl : lowerHistoryPaths[1071]? = some M7ContinueSep17.Initial20260918.B1070_1075.path1072 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 75 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1072
  · have hl : lowerHistoryPaths[1072]? = some M7ContinueSep17.Initial20260918.B1070_1075.path1073 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 76 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1073
  · have hl : lowerHistoryPaths[1073]? = some M7ContinueSep17.Initial20260918.B1070_1075.path1074 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 77 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1074
  · have hl : lowerHistoryPaths[1074]? = some M7ContinueSep17.Initial20260918.B1070_1075.path1075 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupX 78 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1075
end M7ContinueSep17.Initial20260918.B1070_1075

#print axioms solution
