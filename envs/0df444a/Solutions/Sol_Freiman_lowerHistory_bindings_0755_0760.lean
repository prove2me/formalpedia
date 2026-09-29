-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0755_0760
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T02:20:24.0037+00:00
-- url     : https://prove2.me/submissions/22166bef-ee31-497d-ae25-0d4d7a80ca5e

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
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def bv3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩⟩⟩
noncomputable def bv5 : CertBound := ⟨true,false,⟨⟨(-4078497/4976303),(3063403/4976303),(0),(0)⟩,⟨(168/409),(1/409),(0),(0)⟩,⟨(223/529),(-1/529),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv6 : CertBound := ⟨true,false,⟨⟨(-2396241/3388429),(1794784/3388429),(0),(0)⟩,⟨(247/649),(1/649),(0),(0)⟩,⟨(177/454),(-1/454),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv13 : CertBound := ⟨true,false,⟨⟨(-271911/1001627),(203584/1001627),(0),(0)⟩,⟨(446/1177),(1/1177),(0),(0)⟩,⟨(651/1702),(-1/1702),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩⟩⟩
noncomputable def bv185 : CertBound := ⟨true,false,⟨⟨(163/5134),(0),(0),(93/25670)⟩,⟨(63/170),(0),(0),(1/510)⟩,⟨(579/1510),(0),(0),(-1/1510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv193 : CertBound := ⟨true,false,⟨⟨(764894239450/22225157013397),(15834078350/66675471040191),(0),(0)⟩,⟨(33275/87889),(-1/87889),(0),(0)⟩,⟨(30631/80882),(1/242646),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv206 : CertBound := ⟨true,false,⟨⟨(7377/165722),(0),(0),(-605/165722)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1341/3526),(0),(0),(-1/3526)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv215 : CertBound := ⟨true,false,⟨⟨(1346119055150/22945528938527),(8480504750/22945528938527),(0),(0)⟩,⟨(19756/52033),(-1/52033),(0),(0)⟩,⟨(53579/141046),(1/141046),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv219 : CertBound := ⟨true,false,⟨⟨(5937/87770),(0),(0),(707/87770)⟩,⟨(251/670),(0),(0),(1/670)⟩,⟨(105/262),(0),(0),(-1/262)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv220 : CertBound := ⟨true,false,⟨⟨(46348286/642787275),(4919669/257114910),(0),(0)⟩,⟨(231/611),(1/1833),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv237 : CertBound := ⟨true,false,⟨⟨(216319037850/1777699342549),(3376499150/5333098027647),(0),(0)⟩,⟨(3247/8507),(-1/25521),(0),(0)⟩,⟨(25537/66838),(1/66838),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv256 : CertBound := ⟨true,false,⟨⟨(1167/4454),(0),(0),(71/4454)⟩,⟨(105/262),(0),(0),(1/262)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv259 : CertBound := ⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv260 : CertBound := ⟨true,false,⟨⟨(31/100),(0),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv265 : CertBound := ⟨true,false,⟨⟨(68586194850/178709345581),(991451750/536128036743),(0),(0)⟩,⟨(1137/2714),(-1/8142),(0),(0)⟩,⟨(8849/21061),(1/21061),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv270 : CertBound := ⟨true,false,⟨⟨(43/94),(0),(0),(37/658)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv275 : CertBound := ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv278 : CertBound := ⟨true,false,⟨⟨(724335/1125901),0,0,(835040/7881307)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv279 : CertBound := ⟨true,false,⟨⟨(5489/8282),0,0,(513/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
noncomputable def bv282 : CertBound := ⟨true,false,⟨⟨(7/10),(0),(0),(1/70)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv284 : CertBound := ⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv286 : CertBound := ⟨true,false,⟨⟨(8603517050/10310778049),(45310050/10310778049),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(3734/9757),(1/9757),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv287 : CertBound := ⟨true,false,⟨⟨(14844131850/16611163283),(-22622450/16611163283),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(553/1429),(1/1429),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv290 : CertBound := ⟨true,false,⟨⟨(5145/4141),0,0,(3196/28987)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv396 : CertBound := ⟨true,true,⟨⟨(163/5134),(0),(0),(93/25670)⟩,⟨(63/170),(0),(0),(1/510)⟩,⟨(579/1510),(0),(0),(-1/1510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv403 : CertBound := ⟨true,true,⟨⟨(7377/165722),(0),(0),(-605/165722)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1341/3526),(0),(0),(-1/3526)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv419 : CertBound := ⟨true,true,⟨⟨(11/47),(0),(0),(4/329)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv420 : CertBound := ⟨true,true,⟨⟨(387/1394),(0),(0),(19/1394)⟩,⟨(29/82),(0),(0),(1/82)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv429 : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv437 : CertBound := ⟨true,true,⟨⟨(1014069/804215),0,0,(167008/804215)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),(0),(0)⟩,⟨(-1/2),(1/2),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv609 : CertBound := ⟨false,false,⟨⟨(14928072/698102327),(107382092/2094306981),(0),(0)⟩,⟨(231/611),(1/1833),(0),(0)⟩,⟨(33275/87889),(-1/87889),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv653 : CertBound := ⟨false,false,⟨⟨(94960/2585869),(259781/2585869),(0),(0)⟩,⟨(446/1177),(1/1177),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv661 : CertBound := ⟨false,false,⟨⟨(367367432500/8652913715931),(90614287000/77876223443379),(0),(0)⟩,⟨(30631/80882),(1/242646),(0),(0)⟩,⟨(4871/12853),(-1/12853),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv706 : CertBound := ⟨false,false,⟨⟨(1878080276500/25150524470163),(39596495000/25150524470163),(0),(0)⟩,⟨(53579/141046),(1/141046),(0),(0)⟩,⟨(2716/7141),(-1/7141),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv728 : CertBound := ⟨false,false,⟨⟨(731824/7179887),(1465575/7179887),(0),(0)⟩,⟨(247/649),(1/649),(0),(0)⟩,⟨(651/1702),(-1/1702),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv761 : CertBound := ⟨false,false,⟨⟨(94485848500/573572201883),(6917647000/5162149816947),(0),(0)⟩,⟨(25537/66838),(1/66838),(0),(0)⟩,⟨(395/1031),(-1/3093),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv769 : CertBound := ⟨false,false,⟨⟨(1101/6157),(0),(0),(128/6157)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(105/262),(0),(0),(-1/262)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv780 : CertBound := ⟨false,false,⟨⟨(8171/31993),(22664/31993),(0),(0)⟩,⟨(89/214),(1/214),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv784 : CertBound := ⟨false,false,⟨⟨(13766/50713),(29019/50713),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv801 : CertBound := ⟨false,false,⟨⟨(254992/735839),(472767/735839),(0),(0)⟩,⟨(89/214),(1/214),(0),(0)⟩,⟨(223/529),(-1/529),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv810 : CertBound := ⟨false,false,⟨⟨(43/94),(0),(0),(37/658)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv811 : CertBound := ⟨false,false,⟨⟨(437151/916486),(1064107/2749458),(0),(0)⟩,⟨(1991/5521),(1/5521),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv815 : CertBound := ⟨false,false,⟨⟨(29268009500/55044587319),(817282000/495401285871),(0),(0)⟩,⟨(8849/21061),(1/21061),(0),(0)⟩,⟨(133/314),(-1/942),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv817 : CertBound := ⟨false,false,⟨⟨(753/1394),(0),(0),(91/1394)⟩,⟨(29/82),(0),(0),(1/82)⟩,⟨(19/34),(0),(0),(-1/34)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv819 : CertBound := ⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv828 : CertBound := ⟨false,false,⟨⟨(5489/8282),0,0,(513/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
noncomputable def bv831 : CertBound := ⟨false,false,⟨⟨(34974/50713),(213073/152139),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv836 : CertBound := ⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv837 : CertBound := ⟨false,false,⟨⟨(16971/22607),(33730/22607),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv846 : CertBound := ⟨false,false,⟨⟨(124480872500/110611274499),(1112783000/110611274499),(0),(0)⟩,⟨(3734/9757),(1/9757),(0),(0)⟩,⟨(177/454),(-1/454),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv848 : CertBound := ⟨false,false,⟨⟨(5145/4141),0,0,(3196/28987)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩
noncomputable def bv849 : CertBound := ⟨false,false,⟨⟨(1014069/804215),0,0,(167008/804215)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv852 : CertBound := ⟨false,false,⟨⟨(123317000/92840319),(-6536000/278520957),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(1809/6094),(1/6094),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv856 : CertBound := ⟨false,false,⟨⟨(3/2),(0),(0),(1/10)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv869 : CertBound := ⟨false,false,⟨⟨(1208703/351923),(-659041/351923),(0),(0)⟩,⟨(7/23),(1/23),(0),(0)⟩,⟨(446/1177),(1/1177),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv876 : CertBound := ⟨false,false,⟨⟨(3317/299),(-1683/299),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(1),(-1/3),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv882 : CertBound := ⟨false,true,⟨⟨(-2688/2497),(2219/2497),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv886 : CertBound := ⟨false,true,⟨⟨(-189063/182281),(473333/546843),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv888 : CertBound := ⟨false,true,⟨⟨(-6713195/6707459),(5674580/6707459),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv897 : CertBound := ⟨false,true,⟨⟨(-19457/64922),(30367/64922),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv898 : CertBound := ⟨false,true,⟨⟨(-2013760/7108959),(3254539/7108959),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv899 : CertBound := ⟨false,true,⟨⟨(-64591922/261590901),(114640810/261590901),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv1078 : CertBound := ⟨false,true,⟨⟨(46348286/642787275),(4919669/257114910),(0),(0)⟩,⟨(231/611),(1/1833),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv1139 : CertBound := ⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv1153 : CertBound := ⟨false,true,⟨⟨(3087972/5986825),(290501/2394730),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(49/109),(-1/109),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1159 : CertBound := ⟨false,true,⟨⟨(724335/1125901),0,0,(835040/7881307)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv1165 : CertBound := ⟨false,true,⟨⟨(14844131850/16611163283),(-22622450/16611163283),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(553/1429),(1/1429),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1170 : CertBound := ⟨false,true,⟨⟨(2386542/2113309),(-1499437/4226618),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
noncomputable def bv1171 : CertBound := ⟨false,true,⟨⟨(184911237/163006657),(-58481983/163006657),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
noncomputable def bv1172 : CertBound := ⟨false,true,⟨⟨(662039/574310),(-212429/574310),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
noncomputable def bv1181 : CertBound := ⟨false,true,⟨⟨(2754444750/2052479143),(-216932250/2052479143),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [bv371,bv843,bv260,bv440] := by
  simpa only [bv371,bv843,bv260,bv440] using BindingNumeric20.initial_base
theorem op1 : lowerHistoryRelaxedGoodness ⟨([2],[3,1]),(false,false)⟩ = some [bv3] := by
  decide +kernel
theorem op2 : lowerHistoryNormalization ([2],[3]) false false = bv856 := by
  norm_num [bv856, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op3 : lowerHistoryNecessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [bv21] := by
  decide +kernel
theorem op4 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = bv1153 := by
  norm_num [bv1153, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op5 : lowerHistoryPull (lowerHistoryH7) ([2],[3]) false = bv275 := by
  norm_num [bv275, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op6 : lowerHistoryPull (lowerHistoryH9) ([2],[3]) false = bv876 := by
  norm_num [bv876, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op7 : lowerHistoryNormalization ([2,2],[3]) true true = bv420 := by
  norm_num [bv420, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op8 : lowerHistoryNecessary ⟨⟨([2,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,2],[3]) = some [bv780] := by
  decide +kernel
theorem op38 : lowerHistoryNormalization ([2,2],[3,1]) false false = bv817 := by
  norm_num [bv817, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op39 : lowerHistoryNecessary ⟨⟨([2,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,2],[3,1]) = some [bv5] := by
  decide +kernel
theorem op33 : lowerHistoryNormalization ([2,2,1],[3,1]) true false = bv256 := by
  norm_num [bv256, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
open BindingNumeric20
theorem op53 : lowerHistoryNecessary ⟨⟨([2,2,2,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [bv801] := by
  decide +kernel
theorem op35 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,2,1],[3,1]) true = bv265 := by
  norm_num [bv265, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op36 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,2,1],[3,1]) true = bv815 := by
  norm_num [bv815, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op37 : lowerHistoryPull (lowerHistoryHN) ([2,2,1],[3,1]) true = bv256 := by
  norm_num [bv256, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op54 : lowerHistoryNormalization ([2,1],[3]) true false = bv282 := by
  norm_num [bv282, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op55 : lowerHistoryNecessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [bv837] := by
  decide +kernel
theorem op56 : lowerHistoryPull (lowerHistoryH2) ([2,1],[3]) true = bv1165 := by
  norm_num [bv1165, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op57 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = bv287 := by
  norm_num [bv287, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op58 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = bv852 := by
  norm_num [bv852, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op59 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = bv811 := by
  norm_num [bv811, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op60 : lowerHistoryPull (lowerHistoryH23) ([2,1],[3]) true = bv1181 := by
  norm_num [bv1181, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op61 : lowerHistoryNormalization ([2,1,1],[3]) true true = bv419 := by
  norm_num [bv419, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def path756 : LowerHistoryPath := ⟨.mixed,72,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),true)],([2,2,2,1],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
noncomputable def raw756 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv420,bv780,bv817,bv5,bv256,bv801,bv265,bv815,bv256],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv876,bv420,bv780,bv817,bv5,bv256,bv801,bv265,bv815,bv256]]
noncomputable def expected756 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv1153,bv420,bv780,bv817,bv5,bv256,bv801,bv265,bv815],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv275,bv876,bv420,bv780,bv817,bv5,bv256,bv801,bv265,bv815]]
theorem structural756 (ops : RootOps19.SourceOps) (b3 b5 b21 b256 b260 b265 b275 b371 b420 b440 b780 b801 b815 b817 b843 b856 b876 b1153 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h4 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2],[3]) false = b1153)
    (h5 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (h6 : ops.pull (lowerHistoryH9) ([2],[3]) false = b876)
    (h7 : ops.normalization ([2,2],[3]) true true = b420)
    (h8 : ops.necessary ⟨⟨([2,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,2],[3]) = some [b780])
    (h38 : ops.normalization ([2,2],[3,1]) false false = b817)
    (h39 : ops.necessary ⟨⟨([2,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,2],[3,1]) = some [b5])
    (h33 : ops.normalization ([2,2,1],[3,1]) true false = b256)
    (h53 : ops.necessary ⟨⟨([2,2,2,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [b801])
    (h35 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,2,1],[3,1]) true = b265)
    (h36 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,2,1],[3,1]) true = b815)
    (h37 : ops.pull (lowerHistoryHN) ([2,2,1],[3,1]) true = b256)
    : RootOps19.eval ops path756 = ([[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b817,b5,b256,b801,b265,b815,b256],[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b817,b5,b256,b801,b265,b815,b256]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path756, h0, h1, h2, h3, h4, h5, h6, h7, h8, h38, h39, h33, h53, h35, h36, h37, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource756 : lowerHistorySourcePremises path756 = raw756.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural756 RootOps19.actualOps bv3 bv5 bv21 bv256 bv260 bv265 bv275 bv371 bv420 bv440 bv780 bv801 bv815 bv817 bv843 bv856 bv876 bv1153 op0 op1 op2 op3 op4 op5 op6 op7 op8 op38 op39 op33 op53 op35 op36 op37
theorem dedup756 : raw756.map List.eraseDups = expected756 := by
  decide +kernel
theorem source756 : lowerHistorySourcePremises path756 = expected756 := (rawSource756).trans (dedup756)
end M7ContinueSep17.Noninitial20260918.B755_760

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
namespace M7ContinueSep17.Noninitial20260918.B755_760
theorem bound3 : lowerHistoryBound 3 = bv3 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[2]? = some bv3 := Eq.refl (some bv3)
  exact (BoundCompact16.global_to_chunk1 2 (by decide)).trans hl
theorem bound5 : lowerHistoryBound 5 = bv5 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[4]? = some bv5 := Eq.refl (some bv5)
  exact (BoundCompact16.global_to_chunk1 4 (by decide)).trans hl
theorem bound6 : lowerHistoryBound 6 = bv6 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[5]? = some bv6 := Eq.refl (some bv6)
  exact (BoundCompact16.global_to_chunk1 5 (by decide)).trans hl
theorem bound13 : lowerHistoryBound 13 = bv13 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[12]? = some bv13 := Eq.refl (some bv13)
  exact (BoundCompact16.global_to_chunk1 12 (by decide)).trans hl
theorem bound21 : lowerHistoryBound 21 = bv21 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[20]? = some bv21 := Eq.refl (some bv21)
  exact (BoundCompact16.global_to_chunk1 20 (by decide)).trans hl
theorem bound185 : lowerHistoryBound 185 = bv185 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[184]? = some bv185 := Eq.refl (some bv185)
  exact (BoundCompact16.global_to_chunk1 184 (by decide)).trans hl
theorem bound193 : lowerHistoryBound 193 = bv193 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[192]? = some bv193 := Eq.refl (some bv193)
  exact (BoundCompact16.global_to_chunk1 192 (by decide)).trans hl
theorem bound206 : lowerHistoryBound 206 = bv206 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[5]? = some bv206 := Eq.refl (some bv206)
  exact (BoundCompact16.global_to_chunk2 5 (by decide)).trans hl
theorem bound215 : lowerHistoryBound 215 = bv215 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[14]? = some bv215 := Eq.refl (some bv215)
  exact (BoundCompact16.global_to_chunk2 14 (by decide)).trans hl
theorem bound219 : lowerHistoryBound 219 = bv219 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[18]? = some bv219 := Eq.refl (some bv219)
  exact (BoundCompact16.global_to_chunk2 18 (by decide)).trans hl
theorem bound220 : lowerHistoryBound 220 = bv220 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[19]? = some bv220 := Eq.refl (some bv220)
  exact (BoundCompact16.global_to_chunk2 19 (by decide)).trans hl
theorem bound237 : lowerHistoryBound 237 = bv237 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[36]? = some bv237 := Eq.refl (some bv237)
  exact (BoundCompact16.global_to_chunk2 36 (by decide)).trans hl
theorem bound256 : lowerHistoryBound 256 = bv256 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[55]? = some bv256 := Eq.refl (some bv256)
  exact (BoundCompact16.global_to_chunk2 55 (by decide)).trans hl
theorem bound259 : lowerHistoryBound 259 = bv259 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[58]? = some bv259 := Eq.refl (some bv259)
  exact (BoundCompact16.global_to_chunk2 58 (by decide)).trans hl
theorem bound260 : lowerHistoryBound 260 = bv260 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[59]? = some bv260 := Eq.refl (some bv260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hl
theorem bound265 : lowerHistoryBound 265 = bv265 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[64]? = some bv265 := Eq.refl (some bv265)
  exact (BoundCompact16.global_to_chunk2 64 (by decide)).trans hl
theorem bound270 : lowerHistoryBound 270 = bv270 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[69]? = some bv270 := Eq.refl (some bv270)
  exact (BoundCompact16.global_to_chunk2 69 (by decide)).trans hl
theorem bound275 : lowerHistoryBound 275 = bv275 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[74]? = some bv275 := Eq.refl (some bv275)
  exact (BoundCompact16.global_to_chunk2 74 (by decide)).trans hl
theorem bound278 : lowerHistoryBound 278 = bv278 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[77]? = some bv278 := Eq.refl (some bv278)
  exact (BoundCompact16.global_to_chunk2 77 (by decide)).trans hl
theorem bound279 : lowerHistoryBound 279 = bv279 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[78]? = some bv279 := Eq.refl (some bv279)
  exact (BoundCompact16.global_to_chunk2 78 (by decide)).trans hl
theorem bound282 : lowerHistoryBound 282 = bv282 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[81]? = some bv282 := Eq.refl (some bv282)
  exact (BoundCompact16.global_to_chunk2 81 (by decide)).trans hl
theorem bound284 : lowerHistoryBound 284 = bv284 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[83]? = some bv284 := Eq.refl (some bv284)
  exact (BoundCompact16.global_to_chunk2 83 (by decide)).trans hl
theorem bound286 : lowerHistoryBound 286 = bv286 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[85]? = some bv286 := Eq.refl (some bv286)
  exact (BoundCompact16.global_to_chunk2 85 (by decide)).trans hl
theorem bound287 : lowerHistoryBound 287 = bv287 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[86]? = some bv287 := Eq.refl (some bv287)
  exact (BoundCompact16.global_to_chunk2 86 (by decide)).trans hl
theorem bound290 : lowerHistoryBound 290 = bv290 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[89]? = some bv290 := Eq.refl (some bv290)
  exact (BoundCompact16.global_to_chunk2 89 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound396 : lowerHistoryBound 396 = bv396 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[195]? = some bv396 := Eq.refl (some bv396)
  exact (BoundCompact16.global_to_chunk2 195 (by decide)).trans hl
theorem bound403 : lowerHistoryBound 403 = bv403 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[2]? = some bv403 := Eq.refl (some bv403)
  exact (BoundCompact16.global_to_chunk3 2 (by decide)).trans hl
theorem bound419 : lowerHistoryBound 419 = bv419 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[18]? = some bv419 := Eq.refl (some bv419)
  exact (BoundCompact16.global_to_chunk3 18 (by decide)).trans hl
theorem bound420 : lowerHistoryBound 420 = bv420 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[19]? = some bv420 := Eq.refl (some bv420)
  exact (BoundCompact16.global_to_chunk3 19 (by decide)).trans hl
theorem bound429 : lowerHistoryBound 429 = bv429 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[28]? = some bv429 := Eq.refl (some bv429)
  exact (BoundCompact16.global_to_chunk3 28 (by decide)).trans hl
theorem bound437 : lowerHistoryBound 437 = bv437 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[36]? = some bv437 := Eq.refl (some bv437)
  exact (BoundCompact16.global_to_chunk3 36 (by decide)).trans hl
theorem bound440 : lowerHistoryBound 440 = bv440 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[39]? = some bv440 := Eq.refl (some bv440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hl
theorem bound609 : lowerHistoryBound 609 = bv609 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[8]? = some bv609 := Eq.refl (some bv609)
  exact (BoundCompact16.global_to_chunk4 8 (by decide)).trans hl
theorem bound653 : lowerHistoryBound 653 = bv653 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[52]? = some bv653 := Eq.refl (some bv653)
  exact (BoundCompact16.global_to_chunk4 52 (by decide)).trans hl
theorem bound661 : lowerHistoryBound 661 = bv661 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[60]? = some bv661 := Eq.refl (some bv661)
  exact (BoundCompact16.global_to_chunk4 60 (by decide)).trans hl
theorem bound706 : lowerHistoryBound 706 = bv706 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[105]? = some bv706 := Eq.refl (some bv706)
  exact (BoundCompact16.global_to_chunk4 105 (by decide)).trans hl
theorem bound728 : lowerHistoryBound 728 = bv728 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[127]? = some bv728 := Eq.refl (some bv728)
  exact (BoundCompact16.global_to_chunk4 127 (by decide)).trans hl
theorem bound761 : lowerHistoryBound 761 = bv761 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[160]? = some bv761 := Eq.refl (some bv761)
  exact (BoundCompact16.global_to_chunk4 160 (by decide)).trans hl
theorem bound769 : lowerHistoryBound 769 = bv769 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[168]? = some bv769 := Eq.refl (some bv769)
  exact (BoundCompact16.global_to_chunk4 168 (by decide)).trans hl
theorem bound780 : lowerHistoryBound 780 = bv780 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[179]? = some bv780 := Eq.refl (some bv780)
  exact (BoundCompact16.global_to_chunk4 179 (by decide)).trans hl
theorem bound784 : lowerHistoryBound 784 = bv784 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[183]? = some bv784 := Eq.refl (some bv784)
  exact (BoundCompact16.global_to_chunk4 183 (by decide)).trans hl
theorem bound801 : lowerHistoryBound 801 = bv801 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[0]? = some bv801 := Eq.refl (some bv801)
  exact (BoundCompact16.global_to_chunk5 0 (by decide)).trans hl
theorem bound810 : lowerHistoryBound 810 = bv810 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[9]? = some bv810 := Eq.refl (some bv810)
  exact (BoundCompact16.global_to_chunk5 9 (by decide)).trans hl
theorem bound811 : lowerHistoryBound 811 = bv811 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[10]? = some bv811 := Eq.refl (some bv811)
  exact (BoundCompact16.global_to_chunk5 10 (by decide)).trans hl
theorem bound815 : lowerHistoryBound 815 = bv815 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[14]? = some bv815 := Eq.refl (some bv815)
  exact (BoundCompact16.global_to_chunk5 14 (by decide)).trans hl
theorem bound817 : lowerHistoryBound 817 = bv817 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[16]? = some bv817 := Eq.refl (some bv817)
  exact (BoundCompact16.global_to_chunk5 16 (by decide)).trans hl
theorem bound819 : lowerHistoryBound 819 = bv819 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[18]? = some bv819 := Eq.refl (some bv819)
  exact (BoundCompact16.global_to_chunk5 18 (by decide)).trans hl
theorem bound828 : lowerHistoryBound 828 = bv828 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[27]? = some bv828 := Eq.refl (some bv828)
  exact (BoundCompact16.global_to_chunk5 27 (by decide)).trans hl
theorem bound831 : lowerHistoryBound 831 = bv831 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[30]? = some bv831 := Eq.refl (some bv831)
  exact (BoundCompact16.global_to_chunk5 30 (by decide)).trans hl
theorem bound836 : lowerHistoryBound 836 = bv836 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[35]? = some bv836 := Eq.refl (some bv836)
  exact (BoundCompact16.global_to_chunk5 35 (by decide)).trans hl
theorem bound837 : lowerHistoryBound 837 = bv837 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[36]? = some bv837 := Eq.refl (some bv837)
  exact (BoundCompact16.global_to_chunk5 36 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound846 : lowerHistoryBound 846 = bv846 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[45]? = some bv846 := Eq.refl (some bv846)
  exact (BoundCompact16.global_to_chunk5 45 (by decide)).trans hl
theorem bound848 : lowerHistoryBound 848 = bv848 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[47]? = some bv848 := Eq.refl (some bv848)
  exact (BoundCompact16.global_to_chunk5 47 (by decide)).trans hl
theorem bound849 : lowerHistoryBound 849 = bv849 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[48]? = some bv849 := Eq.refl (some bv849)
  exact (BoundCompact16.global_to_chunk5 48 (by decide)).trans hl
theorem bound852 : lowerHistoryBound 852 = bv852 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[51]? = some bv852 := Eq.refl (some bv852)
  exact (BoundCompact16.global_to_chunk5 51 (by decide)).trans hl
theorem bound856 : lowerHistoryBound 856 = bv856 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[55]? = some bv856 := Eq.refl (some bv856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hl
theorem bound869 : lowerHistoryBound 869 = bv869 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[68]? = some bv869 := Eq.refl (some bv869)
  exact (BoundCompact16.global_to_chunk5 68 (by decide)).trans hl
theorem bound876 : lowerHistoryBound 876 = bv876 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[75]? = some bv876 := Eq.refl (some bv876)
  exact (BoundCompact16.global_to_chunk5 75 (by decide)).trans hl
theorem bound882 : lowerHistoryBound 882 = bv882 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[81]? = some bv882 := Eq.refl (some bv882)
  exact (BoundCompact16.global_to_chunk5 81 (by decide)).trans hl
theorem bound886 : lowerHistoryBound 886 = bv886 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[85]? = some bv886 := Eq.refl (some bv886)
  exact (BoundCompact16.global_to_chunk5 85 (by decide)).trans hl
theorem bound888 : lowerHistoryBound 888 = bv888 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[87]? = some bv888 := Eq.refl (some bv888)
  exact (BoundCompact16.global_to_chunk5 87 (by decide)).trans hl
theorem bound897 : lowerHistoryBound 897 = bv897 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[96]? = some bv897 := Eq.refl (some bv897)
  exact (BoundCompact16.global_to_chunk5 96 (by decide)).trans hl
theorem bound898 : lowerHistoryBound 898 = bv898 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[97]? = some bv898 := Eq.refl (some bv898)
  exact (BoundCompact16.global_to_chunk5 97 (by decide)).trans hl
theorem bound899 : lowerHistoryBound 899 = bv899 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[98]? = some bv899 := Eq.refl (some bv899)
  exact (BoundCompact16.global_to_chunk5 98 (by decide)).trans hl
theorem bound1078 : lowerHistoryBound 1078 = bv1078 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[77]? = some bv1078 := Eq.refl (some bv1078)
  exact (BoundCompact16.global_to_chunk6 77).trans hl
theorem bound1139 : lowerHistoryBound 1139 = bv1139 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[138]? = some bv1139 := Eq.refl (some bv1139)
  exact (BoundCompact16.global_to_chunk6 138).trans hl
theorem bound1153 : lowerHistoryBound 1153 = bv1153 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[152]? = some bv1153 := Eq.refl (some bv1153)
  exact (BoundCompact16.global_to_chunk6 152).trans hl
theorem bound1159 : lowerHistoryBound 1159 = bv1159 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[158]? = some bv1159 := Eq.refl (some bv1159)
  exact (BoundCompact16.global_to_chunk6 158).trans hl
theorem bound1165 : lowerHistoryBound 1165 = bv1165 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[164]? = some bv1165 := Eq.refl (some bv1165)
  exact (BoundCompact16.global_to_chunk6 164).trans hl
theorem bound1170 : lowerHistoryBound 1170 = bv1170 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[169]? = some bv1170 := Eq.refl (some bv1170)
  exact (BoundCompact16.global_to_chunk6 169).trans hl
theorem bound1171 : lowerHistoryBound 1171 = bv1171 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[170]? = some bv1171 := Eq.refl (some bv1171)
  exact (BoundCompact16.global_to_chunk6 170).trans hl
theorem bound1172 : lowerHistoryBound 1172 = bv1172 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[171]? = some bv1172 := Eq.refl (some bv1172)
  exact (BoundCompact16.global_to_chunk6 171).trans hl
theorem bound1181 : lowerHistoryBound 1181 = bv1181 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[180]? = some bv1181 := Eq.refl (some bv1181)
  exact (BoundCompact16.global_to_chunk6 180).trans hl
end M7ContinueSep17.Noninitial20260918.B755_760

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
theorem catalogListM : catalogRecords .mixed = [
⟨.mixed,1,0,(-1),false,223,1072⟩,
⟨.mixed,2,0,(-1),false,231,1084⟩,
⟨.mixed,2,1,(-1),false,229,1084⟩,
⟨.mixed,3,0,(-1),false,235,1108⟩,
⟨.mixed,4,0,(-1),false,120,1078⟩,
⟨.mixed,5,0,(-1),false,132,1096⟩,
⟨.mixed,5,1,(-1),false,129,1096⟩,
⟨.mixed,6,0,(-1),false,157,1120⟩,
⟨.mixed,7,0,(-1),false,342,584⟩,
⟨.mixed,8,0,(-1),false,341,596⟩,
⟨.mixed,8,1,(-1),false,340,596⟩,
⟨.mixed,9,0,(-1),false,343,632⟩,
⟨.mixed,10,0,(-1),false,435,1013⟩,
⟨.mixed,11,0,(-1),false,224,650⟩,
⟨.mixed,12,0,(-1),false,232,692⟩,
⟨.mixed,12,1,(-1),false,230,692⟩,
⟨.mixed,13,0,(-1),false,236,752⟩,
⟨.mixed,14,0,(-1),false,276,590⟩,
⟨.mixed,14,1,(-1),false,274,590⟩,
⟨.mixed,14,2,(-1),false,275,590⟩,
⟨.mixed,14,3,(-1),false,273,590⟩,
⟨.mixed,15,0,(-1),false,272,614⟩,
⟨.mixed,15,1,(-1),false,268,614⟩,
⟨.mixed,15,2,(-1),false,270,614⟩,
⟨.mixed,15,3,(-1),false,266,614⟩,
⟨.mixed,15,4,(-1),false,271,614⟩,
⟨.mixed,15,5,(-1),false,267,614⟩,
⟨.mixed,15,6,(-1),false,269,614⟩,
⟨.mixed,15,7,(-1),false,265,614⟩,
⟨.mixed,16,0,(-1),false,280,662⟩,
⟨.mixed,16,1,(-1),false,278,662⟩,
⟨.mixed,16,2,(-1),false,279,662⟩,
⟨.mixed,16,3,(-1),false,277,662⟩,
⟨.mixed,17,0,(-1),false,439,1030⟩,
⟨.mixed,17,1,(-1),false,437,722⟩,
⟨.mixed,17,2,(-1),false,438,1030⟩,
⟨.mixed,17,3,(-1),false,436,722⟩,
⟨.mixed,18,0,(-1),false,121,686⟩,
⟨.mixed,18,1,(-1),false,119,686⟩,
⟨.mixed,19,0,(-1),false,133,728⟩,
⟨.mixed,19,1,(-1),false,130,728⟩,
⟨.mixed,19,2,(-1),false,131,728⟩,
⟨.mixed,19,3,(-1),false,128,728⟩,
⟨.mixed,20,0,(-1),false,158,776⟩,
⟨.mixed,20,1,(-1),false,156,776⟩,
⟨.mixed,21,0,(-1),false,188,626⟩,
⟨.mixed,21,1,(-1),false,187,80⟩,
⟨.mixed,22,0,(-1),false,186,656⟩,
⟨.mixed,22,1,(-1),false,184,656⟩,
⟨.mixed,22,2,(-1),false,185,86⟩,
⟨.mixed,22,3,(-1),false,183,86⟩,
⟨.mixed,23,0,(-1),false,192,698⟩,
⟨.mixed,23,1,(-1),false,191,92⟩,
⟨.mixed,24,0,0,false,492,72⟩,
⟨.mixed,24,0,1,false,484,72⟩,
⟨.mixed,24,0,2,false,460,28⟩,
⟨.mixed,24,0,3,false,480,558⟩,
⟨.mixed,24,0,4,false,482,175⟩,
⟨.mixed,24,0,5,false,449,76⟩,
⟨.mixed,24,0,6,false,447,76⟩,
⟨.mixed,24,0,7,false,441,32⟩,
⟨.mixed,24,0,8,false,445,562⟩,
⟨.mixed,24,0,9,false,446,179⟩,
⟨.mixed,24,0,10,false,488,314⟩,
⟨.mixed,24,0,11,false,472,314⟩,
⟨.mixed,24,0,12,false,456,18⟩,
⟨.mixed,24,0,13,false,468,548⟩,
⟨.mixed,24,0,14,false,469,165⟩,
⟨.mixed,24,0,15,false,489,60⟩,
⟨.mixed,24,0,16,false,473,60⟩,
⟨.mixed,24,0,17,false,457,22⟩,
⟨.mixed,24,0,18,false,470,552⟩,
⟨.mixed,24,0,19,false,471,169⟩,
⟨.mixed,24,1,0,false,490,155⟩,
⟨.mixed,24,1,1,false,478,155⟩,
⟨.mixed,24,1,2,false,458,28⟩,
⟨.mixed,24,1,3,false,474,558⟩,
⟨.mixed,24,1,4,false,476,175⟩,
⟨.mixed,24,1,5,false,448,159⟩,
⟨.mixed,24,1,6,false,444,159⟩,
⟨.mixed,24,1,7,false,440,32⟩,
⟨.mixed,24,1,8,false,442,562⟩,
⟨.mixed,24,1,9,false,443,179⟩,
⟨.mixed,24,1,10,false,486,314⟩,
⟨.mixed,24,1,11,false,466,314⟩,
⟨.mixed,24,1,12,false,454,18⟩,
⟨.mixed,24,1,13,false,462,548⟩,
⟨.mixed,24,1,14,false,463,165⟩,
⟨.mixed,24,1,15,false,487,113⟩,
⟨.mixed,24,1,16,false,467,113⟩,
⟨.mixed,24,1,17,false,455,22⟩,
⟨.mixed,24,1,18,false,464,552⟩,
⟨.mixed,24,1,19,false,465,169⟩,
⟨.mixed,25,0,(-1),false,45,746⟩,
⟨.mixed,26,0,(-1),false,44,764⟩,
⟨.mixed,26,1,(-1),false,43,764⟩,
⟨.mixed,27,0,0,false,74,72⟩,
⟨.mixed,27,0,1,false,70,72⟩,
⟨.mixed,27,0,2,false,58,28⟩,
⟨.mixed,27,0,3,false,66,558⟩,
⟨.mixed,27,0,4,false,68,175⟩,
⟨.mixed,27,0,5,false,50,76⟩,
⟨.mixed,27,0,6,false,49,76⟩,
⟨.mixed,27,0,7,false,46,32⟩,
⟨.mixed,27,0,8,false,47,562⟩,
⟨.mixed,27,0,9,false,48,179⟩,
⟨.mixed,27,0,10,false,72,314⟩,
⟨.mixed,27,0,11,false,64,314⟩,
⟨.mixed,27,0,12,false,56,18⟩,
⟨.mixed,27,0,13,false,60,548⟩,
⟨.mixed,27,0,14,false,61,165⟩,
⟨.mixed,27,0,15,false,73,60⟩,
⟨.mixed,27,0,16,false,65,60⟩,
⟨.mixed,27,0,17,false,57,22⟩,
⟨.mixed,27,0,18,false,62,552⟩,
⟨.mixed,27,0,19,false,63,169⟩,
⟨.mixed,28,0,(-1),false,415,746⟩,
⟨.mixed,28,1,(-1),false,410,746⟩,
⟨.mixed,28,2,(-1),false,416,746⟩,
⟨.mixed,29,0,(-1),false,377,608⟩,
⟨.mixed,29,1,(-1),false,373,608⟩,
⟨.mixed,29,2,(-1),false,376,608⟩,
⟨.mixed,29,3,(-1),false,372,608⟩,
⟨.mixed,29,4,(-1),false,378,608⟩,
⟨.mixed,29,5,(-1),false,374,608⟩,
⟨.mixed,30,0,(-1),false,381,644⟩,
⟨.mixed,30,1,(-1),false,380,644⟩,
⟨.mixed,30,2,(-1),false,382,644⟩,
⟨.mixed,31,0,(-1),false,412,764⟩,
⟨.mixed,32,0,(-1),false,317,602⟩,
⟨.mixed,33,0,(-1),false,315,620⟩,
⟨.mixed,33,1,(-1),false,313,620⟩,
⟨.mixed,34,0,(-1),false,319,668⟩,
⟨.mixed,35,0,(-1),false,33,746⟩,
⟨.mixed,36,0,(-1),false,32,764⟩,
⟨.mixed,36,1,(-1),false,31,764⟩,
⟨.mixed,37,0,(-1),false,35,54⟩,
⟨.mixed,38,0,(-1),false,379,608⟩,
⟨.mixed,38,1,(-1),false,375,608⟩,
⟨.mixed,39,0,(-1),false,383,644⟩,
⟨.mixed,40,0,(-1),false,417,746⟩,
⟨.mixed,41,0,(-1),false,318,602⟩,
⟨.mixed,42,0,(-1),false,316,620⟩,
⟨.mixed,42,1,(-1),false,314,620⟩,
⟨.mixed,43,0,(-1),false,320,668⟩,
⟨.mixed,44,0,(-1),false,413,1042⟩,
⟨.mixed,45,0,(-1),false,167,626⟩,
⟨.mixed,46,0,(-1),false,166,656⟩,
⟨.mixed,46,1,(-1),false,165,656⟩,
⟨.mixed,47,0,(-1),false,169,698⟩,
⟨.mixed,48,0,(-1),false,414,54⟩,
⟨.mixed,49,0,(-1),false,9,203⟩,
⟨.mixed,50,0,(-1),false,8,209⟩,
⟨.mixed,50,1,(-1),false,7,209⟩,
⟨.mixed,51,0,(-1),false,11,215⟩,
⟨.mixed,52,0,(-1),false,517,296⟩,
⟨.mixed,53,0,(-1),false,223,1071⟩,
⟨.mixed,54,0,(-1),false,231,1083⟩,
⟨.mixed,54,1,(-1),false,229,1083⟩,
⟨.mixed,55,0,(-1),false,235,1107⟩,
⟨.mixed,56,0,(-1),false,120,1077⟩,
⟨.mixed,57,0,(-1),false,132,1095⟩,
⟨.mixed,57,1,(-1),false,129,1095⟩,
⟨.mixed,58,0,(-1),false,157,1119⟩,
⟨.mixed,59,0,(-1),false,342,583⟩,
⟨.mixed,60,0,(-1),false,341,595⟩,
⟨.mixed,60,1,(-1),false,340,595⟩,
⟨.mixed,61,0,(-1),false,343,631⟩,
⟨.mixed,62,0,(-1),false,435,1012⟩,
⟨.mixed,63,0,(-1),false,224,649⟩,
⟨.mixed,64,0,(-1),false,232,691⟩,
⟨.mixed,64,1,(-1),false,230,691⟩,
⟨.mixed,65,0,(-1),false,236,751⟩,
⟨.mixed,66,0,(-1),false,276,589⟩,
⟨.mixed,66,1,(-1),false,274,589⟩,
⟨.mixed,66,2,(-1),false,275,589⟩,
⟨.mixed,66,3,(-1),false,273,589⟩,
⟨.mixed,67,0,(-1),false,272,613⟩,
⟨.mixed,67,1,(-1),false,268,613⟩,
⟨.mixed,67,2,(-1),false,270,613⟩,
⟨.mixed,67,3,(-1),false,266,613⟩,
⟨.mixed,67,4,(-1),false,271,613⟩,
⟨.mixed,67,5,(-1),false,267,613⟩,
⟨.mixed,67,6,(-1),false,269,613⟩,
⟨.mixed,67,7,(-1),false,265,613⟩,
⟨.mixed,68,0,(-1),false,280,661⟩,
⟨.mixed,68,1,(-1),false,278,661⟩,
⟨.mixed,68,2,(-1),false,279,661⟩,
⟨.mixed,68,3,(-1),false,277,661⟩,
⟨.mixed,69,0,(-1),false,439,1029⟩,
⟨.mixed,69,1,(-1),false,437,721⟩,
⟨.mixed,69,2,(-1),false,438,1029⟩,
⟨.mixed,69,3,(-1),false,436,721⟩,
⟨.mixed,70,0,(-1),false,121,685⟩,
⟨.mixed,70,1,(-1),false,119,685⟩,
⟨.mixed,71,0,(-1),false,133,727⟩,
⟨.mixed,71,1,(-1),false,130,727⟩,
⟨.mixed,71,2,(-1),false,131,727⟩,
⟨.mixed,71,3,(-1),false,128,727⟩,
⟨.mixed,72,0,(-1),false,158,775⟩,
⟨.mixed,72,1,(-1),false,156,775⟩,
⟨.mixed,73,0,(-1),false,188,625⟩,
⟨.mixed,73,1,(-1),false,187,79⟩,
⟨.mixed,74,0,(-1),false,186,655⟩,
⟨.mixed,74,1,(-1),false,184,655⟩,
⟨.mixed,74,2,(-1),false,185,85⟩,
⟨.mixed,74,3,(-1),false,183,85⟩,
⟨.mixed,75,0,(-1),false,192,697⟩,
⟨.mixed,75,1,(-1),false,191,91⟩,
⟨.mixed,76,0,0,false,492,71⟩,
⟨.mixed,76,0,1,false,484,71⟩,
⟨.mixed,76,0,2,false,460,27⟩,
⟨.mixed,76,0,3,false,480,557⟩,
⟨.mixed,76,0,4,false,482,174⟩,
⟨.mixed,76,0,5,false,449,75⟩,
⟨.mixed,76,0,6,false,447,75⟩,
⟨.mixed,76,0,7,false,441,31⟩,
⟨.mixed,76,0,8,false,445,561⟩,
⟨.mixed,76,0,9,false,446,178⟩,
⟨.mixed,76,0,10,false,488,313⟩,
⟨.mixed,76,0,11,false,472,313⟩,
⟨.mixed,76,0,12,false,456,17⟩,
⟨.mixed,76,0,13,false,468,547⟩,
⟨.mixed,76,0,14,false,469,164⟩,
⟨.mixed,76,0,15,false,489,59⟩,
⟨.mixed,76,0,16,false,473,59⟩,
⟨.mixed,76,0,17,false,457,21⟩,
⟨.mixed,76,0,18,false,470,551⟩,
⟨.mixed,76,0,19,false,471,168⟩,
⟨.mixed,76,1,0,false,490,154⟩,
⟨.mixed,76,1,1,false,478,154⟩,
⟨.mixed,76,1,2,false,458,27⟩,
⟨.mixed,76,1,3,false,474,557⟩,
⟨.mixed,76,1,4,false,476,174⟩,
⟨.mixed,76,1,5,false,448,158⟩,
⟨.mixed,76,1,6,false,444,158⟩,
⟨.mixed,76,1,7,false,440,31⟩,
⟨.mixed,76,1,8,false,442,561⟩,
⟨.mixed,76,1,9,false,443,178⟩,
⟨.mixed,76,1,10,false,486,109⟩,
⟨.mixed,76,1,11,false,466,109⟩,
⟨.mixed,76,1,12,false,454,17⟩,
⟨.mixed,76,1,13,false,462,547⟩,
⟨.mixed,76,1,14,false,463,164⟩,
⟨.mixed,76,1,15,false,487,112⟩,
⟨.mixed,76,1,16,false,467,112⟩,
⟨.mixed,76,1,17,false,455,21⟩,
⟨.mixed,76,1,18,false,464,551⟩,
⟨.mixed,76,1,19,false,465,168⟩,
⟨.mixed,77,0,(-1),false,45,745⟩,
⟨.mixed,78,0,(-1),false,44,763⟩,
⟨.mixed,78,1,(-1),false,43,763⟩,
⟨.mixed,79,0,0,false,74,71⟩,
⟨.mixed,79,0,1,false,70,71⟩,
⟨.mixed,79,0,2,false,58,27⟩,
⟨.mixed,79,0,3,false,66,557⟩,
⟨.mixed,79,0,4,false,68,174⟩,
⟨.mixed,79,0,5,false,50,75⟩,
⟨.mixed,79,0,6,false,49,75⟩,
⟨.mixed,79,0,7,false,46,31⟩,
⟨.mixed,79,0,8,false,47,561⟩,
⟨.mixed,79,0,9,false,48,178⟩,
⟨.mixed,79,0,10,false,72,313⟩,
⟨.mixed,79,0,11,false,64,313⟩,
⟨.mixed,79,0,12,false,56,17⟩,
⟨.mixed,79,0,13,false,60,547⟩,
⟨.mixed,79,0,14,false,61,164⟩,
⟨.mixed,79,0,15,false,73,59⟩,
⟨.mixed,79,0,16,false,65,59⟩,
⟨.mixed,79,0,17,false,57,21⟩,
⟨.mixed,79,0,18,false,62,551⟩,
⟨.mixed,79,0,19,false,63,168⟩,
⟨.mixed,80,0,(-1),false,415,745⟩,
⟨.mixed,80,1,(-1),false,410,745⟩,
⟨.mixed,80,2,(-1),false,416,745⟩,
⟨.mixed,81,0,(-1),false,377,607⟩,
⟨.mixed,81,1,(-1),false,373,607⟩,
⟨.mixed,81,2,(-1),false,376,607⟩,
⟨.mixed,81,3,(-1),false,372,607⟩,
⟨.mixed,81,4,(-1),false,378,607⟩,
⟨.mixed,81,5,(-1),false,374,607⟩,
⟨.mixed,82,0,(-1),false,381,643⟩,
⟨.mixed,82,1,(-1),false,380,643⟩,
⟨.mixed,82,2,(-1),false,382,643⟩,
⟨.mixed,83,0,(-1),false,412,763⟩,
⟨.mixed,84,0,(-1),false,317,601⟩,
⟨.mixed,85,0,(-1),false,315,619⟩,
⟨.mixed,85,1,(-1),false,313,619⟩,
⟨.mixed,86,0,(-1),false,319,667⟩,
⟨.mixed,87,0,(-1),false,33,745⟩,
⟨.mixed,88,0,(-1),false,32,763⟩,
⟨.mixed,88,1,(-1),false,31,763⟩,
⟨.mixed,89,0,(-1),false,35,53⟩,
⟨.mixed,90,0,(-1),false,379,607⟩,
⟨.mixed,90,1,(-1),false,375,607⟩,
⟨.mixed,91,0,(-1),false,383,643⟩,
⟨.mixed,92,0,(-1),false,417,745⟩,
⟨.mixed,93,0,(-1),false,318,601⟩,
⟨.mixed,94,0,(-1),false,316,619⟩,
⟨.mixed,94,1,(-1),false,314,619⟩,
⟨.mixed,95,0,(-1),false,320,667⟩,
⟨.mixed,96,0,(-1),false,413,1041⟩,
⟨.mixed,97,0,(-1),false,167,625⟩,
⟨.mixed,98,0,(-1),false,166,655⟩,
⟨.mixed,98,1,(-1),false,165,655⟩,
⟨.mixed,99,0,(-1),false,169,697⟩,
⟨.mixed,100,0,(-1),false,414,53⟩,
⟨.mixed,101,0,(-1),false,9,202⟩,
⟨.mixed,102,0,(-1),false,8,208⟩,
⟨.mixed,102,1,(-1),false,7,208⟩,
⟨.mixed,103,0,(-1),false,11,220⟩,
⟨.mixed,104,0,(-1),false,517,295⟩,
⟨.mixed,105,0,(-1),false,223,1069⟩,
⟨.mixed,106,0,(-1),false,231,1081⟩,
⟨.mixed,106,1,(-1),false,229,1081⟩,
⟨.mixed,107,0,(-1),false,235,1105⟩,
⟨.mixed,108,0,(-1),false,120,1075⟩,
⟨.mixed,109,0,(-1),false,132,1093⟩,
⟨.mixed,109,1,(-1),false,129,1093⟩,
⟨.mixed,110,0,(-1),false,157,1117⟩,
⟨.mixed,111,0,(-1),false,342,581⟩,
⟨.mixed,112,0,(-1),false,341,593⟩,
⟨.mixed,112,1,(-1),false,340,593⟩,
⟨.mixed,113,0,(-1),false,343,629⟩,
⟨.mixed,114,0,(-1),false,435,1010⟩,
⟨.mixed,115,0,(-1),false,224,647⟩,
⟨.mixed,116,0,(-1),false,232,689⟩,
⟨.mixed,116,1,(-1),false,230,689⟩,
⟨.mixed,117,0,(-1),false,236,749⟩,
⟨.mixed,118,0,(-1),false,276,587⟩,
⟨.mixed,118,1,(-1),false,274,587⟩,
⟨.mixed,118,2,(-1),false,275,587⟩,
⟨.mixed,118,3,(-1),false,273,587⟩,
⟨.mixed,119,0,(-1),false,272,611⟩,
⟨.mixed,119,1,(-1),false,268,611⟩,
⟨.mixed,119,2,(-1),false,270,611⟩,
⟨.mixed,119,3,(-1),false,266,611⟩,
⟨.mixed,119,4,(-1),false,271,611⟩,
⟨.mixed,119,5,(-1),false,267,611⟩,
⟨.mixed,119,6,(-1),false,269,611⟩,
⟨.mixed,119,7,(-1),false,265,611⟩,
⟨.mixed,120,0,(-1),false,280,659⟩,
⟨.mixed,120,1,(-1),false,278,659⟩,
⟨.mixed,120,2,(-1),false,279,659⟩,
⟨.mixed,120,3,(-1),false,277,659⟩,
⟨.mixed,121,0,(-1),false,439,1027⟩,
⟨.mixed,121,1,(-1),false,437,719⟩,
⟨.mixed,121,2,(-1),false,438,1027⟩,
⟨.mixed,121,3,(-1),false,436,719⟩,
⟨.mixed,122,0,(-1),false,121,683⟩,
⟨.mixed,122,1,(-1),false,119,683⟩,
⟨.mixed,123,0,(-1),false,133,725⟩,
⟨.mixed,123,1,(-1),false,130,725⟩,
⟨.mixed,123,2,(-1),false,131,725⟩,
⟨.mixed,123,3,(-1),false,128,725⟩,
⟨.mixed,124,0,(-1),false,158,773⟩,
⟨.mixed,124,1,(-1),false,156,773⟩,
⟨.mixed,125,0,(-1),false,188,623⟩,
⟨.mixed,125,1,(-1),false,187,77⟩,
⟨.mixed,126,0,(-1),false,186,653⟩,
⟨.mixed,126,1,(-1),false,184,653⟩,
⟨.mixed,126,2,(-1),false,185,83⟩,
⟨.mixed,126,3,(-1),false,183,83⟩,
⟨.mixed,127,0,(-1),false,192,695⟩,
⟨.mixed,127,1,(-1),false,191,89⟩,
⟨.mixed,128,0,0,false,492,69⟩,
⟨.mixed,128,0,1,false,484,69⟩,
⟨.mixed,128,0,2,false,460,25⟩,
⟨.mixed,128,0,3,false,480,555⟩,
⟨.mixed,128,0,4,false,482,172⟩,
⟨.mixed,128,0,5,false,449,73⟩,
⟨.mixed,128,0,6,false,447,73⟩,
⟨.mixed,128,0,7,false,441,29⟩,
⟨.mixed,128,0,8,false,445,559⟩,
⟨.mixed,128,0,9,false,446,176⟩,
⟨.mixed,128,0,10,false,488,311⟩,
⟨.mixed,128,0,11,false,472,311⟩,
⟨.mixed,128,0,12,false,456,15⟩,
⟨.mixed,128,0,13,false,468,545⟩,
⟨.mixed,128,0,14,false,469,162⟩,
⟨.mixed,128,0,15,false,489,57⟩,
⟨.mixed,128,0,16,false,473,57⟩,
⟨.mixed,128,0,17,false,457,19⟩,
⟨.mixed,128,0,18,false,470,549⟩,
⟨.mixed,128,0,19,false,471,166⟩,
⟨.mixed,128,1,0,false,490,152⟩,
⟨.mixed,128,1,1,false,478,152⟩,
⟨.mixed,128,1,2,false,458,25⟩,
⟨.mixed,128,1,3,false,474,555⟩,
⟨.mixed,128,1,4,false,476,172⟩,
⟨.mixed,128,1,5,false,448,156⟩,
⟨.mixed,128,1,6,false,444,156⟩,
⟨.mixed,128,1,7,false,440,29⟩,
⟨.mixed,128,1,8,false,442,559⟩,
⟨.mixed,128,1,9,false,443,176⟩,
⟨.mixed,128,1,10,false,486,107⟩,
⟨.mixed,128,1,11,false,466,107⟩,
⟨.mixed,128,1,12,false,454,15⟩,
⟨.mixed,128,1,13,false,462,545⟩,
⟨.mixed,128,1,14,false,463,162⟩,
⟨.mixed,128,1,15,false,487,110⟩,
⟨.mixed,128,1,16,false,467,110⟩,
⟨.mixed,128,1,17,false,455,19⟩,
⟨.mixed,128,1,18,false,464,549⟩,
⟨.mixed,128,1,19,false,465,166⟩,
⟨.mixed,129,0,(-1),false,45,743⟩,
⟨.mixed,130,0,(-1),false,44,761⟩,
⟨.mixed,130,1,(-1),false,43,761⟩,
⟨.mixed,131,0,0,false,74,69⟩,
⟨.mixed,131,0,1,false,70,69⟩,
⟨.mixed,131,0,2,false,58,25⟩,
⟨.mixed,131,0,3,false,66,555⟩,
⟨.mixed,131,0,4,false,68,172⟩,
⟨.mixed,131,0,5,false,50,73⟩,
⟨.mixed,131,0,6,false,49,73⟩,
⟨.mixed,131,0,7,false,46,29⟩,
⟨.mixed,131,0,8,false,47,559⟩,
⟨.mixed,131,0,9,false,48,176⟩,
⟨.mixed,131,0,10,false,72,311⟩,
⟨.mixed,131,0,11,false,64,311⟩,
⟨.mixed,131,0,12,false,56,15⟩,
⟨.mixed,131,0,13,false,60,545⟩,
⟨.mixed,131,0,14,false,61,162⟩,
⟨.mixed,131,0,15,false,73,57⟩,
⟨.mixed,131,0,16,false,65,57⟩,
⟨.mixed,131,0,17,false,57,19⟩,
⟨.mixed,131,0,18,false,62,549⟩,
⟨.mixed,131,0,19,false,63,166⟩,
⟨.mixed,132,0,(-1),false,415,743⟩,
⟨.mixed,132,1,(-1),false,410,743⟩,
⟨.mixed,132,2,(-1),false,416,743⟩,
⟨.mixed,133,0,(-1),false,377,605⟩,
⟨.mixed,133,1,(-1),false,373,605⟩,
⟨.mixed,133,2,(-1),false,376,605⟩,
⟨.mixed,133,3,(-1),false,372,605⟩,
⟨.mixed,133,4,(-1),false,378,605⟩,
⟨.mixed,133,5,(-1),false,374,605⟩,
⟨.mixed,134,0,(-1),false,381,641⟩,
⟨.mixed,134,1,(-1),false,380,641⟩,
⟨.mixed,134,2,(-1),false,382,641⟩,
⟨.mixed,135,0,(-1),false,412,761⟩,
⟨.mixed,136,0,(-1),false,317,599⟩,
⟨.mixed,137,0,(-1),false,315,617⟩,
⟨.mixed,137,1,(-1),false,313,617⟩,
⟨.mixed,138,0,(-1),false,319,665⟩,
⟨.mixed,139,0,(-1),false,33,743⟩,
⟨.mixed,140,0,(-1),false,32,761⟩,
⟨.mixed,140,1,(-1),false,31,761⟩,
⟨.mixed,141,0,(-1),false,35,51⟩,
⟨.mixed,142,0,(-1),false,379,605⟩,
⟨.mixed,142,1,(-1),false,375,605⟩,
⟨.mixed,143,0,(-1),false,383,641⟩,
⟨.mixed,144,0,(-1),false,417,743⟩,
⟨.mixed,145,0,(-1),false,318,599⟩,
⟨.mixed,146,0,(-1),false,316,617⟩,
⟨.mixed,146,1,(-1),false,314,617⟩,
⟨.mixed,147,0,(-1),false,320,665⟩,
⟨.mixed,148,0,(-1),false,413,1039⟩,
⟨.mixed,149,0,(-1),false,167,623⟩,
⟨.mixed,150,0,(-1),false,166,653⟩,
⟨.mixed,150,1,(-1),false,165,653⟩,
⟨.mixed,151,0,(-1),false,169,695⟩,
⟨.mixed,152,0,(-1),false,414,51⟩,
⟨.mixed,153,0,(-1),false,9,200⟩,
⟨.mixed,154,0,(-1),false,8,206⟩,
⟨.mixed,154,1,(-1),false,7,206⟩,
⟨.mixed,155,0,(-1),false,11,218⟩,
⟨.mixed,156,0,(-1),false,517,293⟩,
⟨.mixed,157,0,(-1),false,223,1073⟩,
⟨.mixed,158,0,(-1),false,231,1085⟩,
⟨.mixed,158,1,(-1),false,229,1085⟩,
⟨.mixed,159,0,(-1),false,235,1109⟩,
⟨.mixed,160,0,(-1),false,120,1079⟩,
⟨.mixed,161,0,(-1),false,132,1097⟩,
⟨.mixed,161,1,(-1),false,129,1097⟩,
⟨.mixed,162,0,(-1),false,157,1121⟩,
⟨.mixed,163,0,(-1),false,342,585⟩,
⟨.mixed,164,0,(-1),false,341,597⟩,
⟨.mixed,164,1,(-1),false,340,597⟩,
⟨.mixed,165,0,(-1),false,343,633⟩,
⟨.mixed,166,0,(-1),false,435,1014⟩,
⟨.mixed,167,0,(-1),false,224,651⟩,
⟨.mixed,168,0,(-1),false,232,693⟩,
⟨.mixed,168,1,(-1),false,230,693⟩,
⟨.mixed,169,0,(-1),false,236,753⟩,
⟨.mixed,170,0,(-1),false,276,591⟩,
⟨.mixed,170,1,(-1),false,274,591⟩,
⟨.mixed,170,2,(-1),false,275,591⟩,
⟨.mixed,170,3,(-1),false,273,591⟩,
⟨.mixed,171,0,(-1),false,272,615⟩,
⟨.mixed,171,1,(-1),false,268,615⟩,
⟨.mixed,171,2,(-1),false,270,615⟩,
⟨.mixed,171,3,(-1),false,266,615⟩,
⟨.mixed,171,4,(-1),false,271,615⟩,
⟨.mixed,171,5,(-1),false,267,615⟩,
⟨.mixed,171,6,(-1),false,269,615⟩,
⟨.mixed,171,7,(-1),false,265,615⟩,
⟨.mixed,172,0,(-1),false,280,663⟩,
⟨.mixed,172,1,(-1),false,278,663⟩,
⟨.mixed,172,2,(-1),false,279,663⟩,
⟨.mixed,172,3,(-1),false,277,663⟩,
⟨.mixed,173,0,(-1),false,439,1031⟩,
⟨.mixed,173,1,(-1),false,437,723⟩,
⟨.mixed,173,2,(-1),false,438,1031⟩,
⟨.mixed,173,3,(-1),false,436,723⟩,
⟨.mixed,174,0,(-1),false,121,687⟩,
⟨.mixed,174,1,(-1),false,119,687⟩,
⟨.mixed,175,0,(-1),false,133,729⟩,
⟨.mixed,175,1,(-1),false,130,729⟩,
⟨.mixed,175,2,(-1),false,131,729⟩,
⟨.mixed,175,3,(-1),false,128,729⟩,
⟨.mixed,176,0,(-1),false,158,777⟩,
⟨.mixed,176,1,(-1),false,156,777⟩,
⟨.mixed,177,0,(-1),false,188,627⟩,
⟨.mixed,177,1,(-1),false,187,81⟩,
⟨.mixed,178,0,(-1),false,186,657⟩,
⟨.mixed,178,1,(-1),false,184,657⟩,
⟨.mixed,178,2,(-1),false,185,87⟩,
⟨.mixed,178,3,(-1),false,183,87⟩,
⟨.mixed,179,0,(-1),false,192,699⟩,
⟨.mixed,179,1,(-1),false,191,93⟩,
⟨.mixed,180,0,0,false,493,61⟩,
⟨.mixed,180,0,1,false,485,61⟩,
⟨.mixed,180,0,2,false,461,23⟩,
⟨.mixed,180,0,3,false,481,553⟩,
⟨.mixed,180,0,4,false,483,170⟩,
⟨.mixed,180,1,0,false,491,114⟩,
⟨.mixed,180,1,1,false,479,114⟩,
⟨.mixed,180,1,2,false,459,23⟩,
⟨.mixed,180,1,3,false,475,553⟩,
⟨.mixed,180,1,4,false,477,170⟩,
⟨.mixed,181,0,(-1),false,45,747⟩,
⟨.mixed,182,0,(-1),false,44,765⟩,
⟨.mixed,182,1,(-1),false,43,765⟩,
⟨.mixed,183,0,0,false,75,61⟩,
⟨.mixed,183,0,1,false,71,61⟩,
⟨.mixed,183,0,2,false,59,23⟩,
⟨.mixed,183,0,3,false,67,553⟩,
⟨.mixed,183,0,4,false,69,170⟩,
⟨.mixed,184,0,(-1),false,415,747⟩,
⟨.mixed,184,1,(-1),false,410,747⟩,
⟨.mixed,184,2,(-1),false,416,747⟩,
⟨.mixed,185,0,(-1),false,377,609⟩,
⟨.mixed,185,1,(-1),false,373,609⟩,
⟨.mixed,185,2,(-1),false,376,609⟩,
⟨.mixed,185,3,(-1),false,372,609⟩,
⟨.mixed,185,4,(-1),false,378,609⟩,
⟨.mixed,185,5,(-1),false,374,609⟩,
⟨.mixed,186,0,(-1),false,381,645⟩,
⟨.mixed,186,1,(-1),false,380,645⟩,
⟨.mixed,186,2,(-1),false,382,645⟩,
⟨.mixed,187,0,(-1),false,412,765⟩,
⟨.mixed,188,0,(-1),false,317,603⟩,
⟨.mixed,189,0,(-1),false,315,621⟩,
⟨.mixed,189,1,(-1),false,313,621⟩,
⟨.mixed,190,0,(-1),false,319,669⟩,
⟨.mixed,191,0,(-1),false,33,747⟩,
⟨.mixed,192,0,(-1),false,32,765⟩,
⟨.mixed,192,1,(-1),false,31,765⟩,
⟨.mixed,193,0,(-1),false,35,55⟩,
⟨.mixed,194,0,(-1),false,379,609⟩,
⟨.mixed,194,1,(-1),false,375,609⟩,
⟨.mixed,195,0,(-1),false,383,645⟩,
⟨.mixed,196,0,(-1),false,417,747⟩,
⟨.mixed,197,0,(-1),false,318,603⟩,
⟨.mixed,198,0,(-1),false,316,621⟩,
⟨.mixed,198,1,(-1),false,314,621⟩,
⟨.mixed,199,0,(-1),false,320,669⟩,
⟨.mixed,200,0,(-1),false,413,1043⟩,
⟨.mixed,201,0,(-1),false,167,627⟩,
⟨.mixed,202,0,(-1),false,166,657⟩,
⟨.mixed,202,1,(-1),false,165,657⟩,
⟨.mixed,203,0,(-1),false,169,699⟩,
⟨.mixed,204,0,(-1),false,414,55⟩,
⟨.mixed,205,0,(-1),false,9,204⟩,
⟨.mixed,206,0,(-1),false,8,210⟩,
⟨.mixed,206,1,(-1),false,7,210⟩,
⟨.mixed,207,0,(-1),false,11,216⟩,
⟨.mixed,208,0,(-1),false,517,297⟩,
⟨.mixed,209,0,(-1),false,223,1070⟩,
⟨.mixed,210,0,(-1),false,231,1082⟩,
⟨.mixed,210,1,(-1),false,229,1082⟩,
⟨.mixed,211,0,(-1),false,235,1106⟩,
⟨.mixed,212,0,(-1),false,120,1076⟩,
⟨.mixed,213,0,(-1),false,132,1094⟩,
⟨.mixed,213,1,(-1),false,129,1094⟩,
⟨.mixed,214,0,(-1),false,157,1118⟩,
⟨.mixed,215,0,(-1),false,342,582⟩,
⟨.mixed,216,0,(-1),false,341,594⟩,
⟨.mixed,216,1,(-1),false,340,594⟩,
⟨.mixed,217,0,(-1),false,343,630⟩,
⟨.mixed,218,0,(-1),false,435,1011⟩,
⟨.mixed,219,0,(-1),false,224,648⟩,
⟨.mixed,220,0,(-1),false,232,690⟩,
⟨.mixed,220,1,(-1),false,230,690⟩,
⟨.mixed,221,0,(-1),false,236,750⟩,
⟨.mixed,222,0,(-1),false,276,588⟩,
⟨.mixed,222,1,(-1),false,274,588⟩,
⟨.mixed,222,2,(-1),false,275,588⟩,
⟨.mixed,222,3,(-1),false,273,588⟩,
⟨.mixed,223,0,(-1),false,272,612⟩,
⟨.mixed,223,1,(-1),false,268,612⟩,
⟨.mixed,223,2,(-1),false,270,612⟩,
⟨.mixed,223,3,(-1),false,266,612⟩,
⟨.mixed,223,4,(-1),false,271,612⟩,
⟨.mixed,223,5,(-1),false,267,612⟩,
⟨.mixed,223,6,(-1),false,269,612⟩,
⟨.mixed,223,7,(-1),false,265,612⟩,
⟨.mixed,224,0,(-1),false,280,660⟩,
⟨.mixed,224,1,(-1),false,278,660⟩,
⟨.mixed,224,2,(-1),false,279,660⟩,
⟨.mixed,224,3,(-1),false,277,660⟩,
⟨.mixed,225,0,(-1),false,439,1028⟩,
⟨.mixed,225,1,(-1),false,437,720⟩,
⟨.mixed,225,2,(-1),false,438,1028⟩,
⟨.mixed,225,3,(-1),false,436,720⟩,
⟨.mixed,226,0,(-1),false,121,684⟩,
⟨.mixed,226,1,(-1),false,119,684⟩,
⟨.mixed,227,0,(-1),false,133,726⟩,
⟨.mixed,227,1,(-1),false,130,726⟩,
⟨.mixed,227,2,(-1),false,131,726⟩,
⟨.mixed,227,3,(-1),false,128,726⟩,
⟨.mixed,228,0,(-1),false,158,774⟩,
⟨.mixed,228,1,(-1),false,156,774⟩,
⟨.mixed,229,0,(-1),false,188,624⟩,
⟨.mixed,229,1,(-1),false,187,78⟩,
⟨.mixed,230,0,(-1),false,186,654⟩,
⟨.mixed,230,1,(-1),false,184,654⟩,
⟨.mixed,230,2,(-1),false,185,84⟩,
⟨.mixed,230,3,(-1),false,183,84⟩,
⟨.mixed,231,0,(-1),false,192,696⟩,
⟨.mixed,231,1,(-1),false,191,90⟩,
⟨.mixed,232,0,0,false,492,70⟩,
⟨.mixed,232,0,1,false,484,70⟩,
⟨.mixed,232,0,2,false,460,26⟩,
⟨.mixed,232,0,3,false,480,556⟩,
⟨.mixed,232,0,4,false,482,173⟩,
⟨.mixed,232,0,5,false,449,74⟩,
⟨.mixed,232,0,6,false,447,74⟩,
⟨.mixed,232,0,7,false,441,30⟩,
⟨.mixed,232,0,8,false,445,560⟩,
⟨.mixed,232,0,9,false,446,177⟩,
⟨.mixed,232,0,10,false,488,312⟩,
⟨.mixed,232,0,11,false,472,312⟩,
⟨.mixed,232,0,12,false,456,16⟩,
⟨.mixed,232,0,13,false,468,546⟩,
⟨.mixed,232,0,14,false,469,163⟩,
⟨.mixed,232,0,15,false,489,58⟩,
⟨.mixed,232,0,16,false,473,58⟩,
⟨.mixed,232,0,17,false,457,20⟩,
⟨.mixed,232,0,18,false,470,550⟩,
⟨.mixed,232,0,19,false,471,167⟩,
⟨.mixed,232,1,0,false,490,153⟩,
⟨.mixed,232,1,1,false,478,153⟩,
⟨.mixed,232,1,2,false,458,26⟩,
⟨.mixed,232,1,3,false,474,556⟩,
⟨.mixed,232,1,4,false,476,173⟩,
⟨.mixed,232,1,5,false,448,157⟩,
⟨.mixed,232,1,6,false,444,157⟩,
⟨.mixed,232,1,7,false,440,30⟩,
⟨.mixed,232,1,8,false,442,560⟩,
⟨.mixed,232,1,9,false,443,177⟩,
⟨.mixed,232,1,10,false,486,108⟩,
⟨.mixed,232,1,11,false,466,108⟩,
⟨.mixed,232,1,12,false,454,16⟩,
⟨.mixed,232,1,13,false,462,546⟩,
⟨.mixed,232,1,14,false,463,163⟩,
⟨.mixed,232,1,15,false,487,111⟩,
⟨.mixed,232,1,16,false,467,111⟩,
⟨.mixed,232,1,17,false,455,20⟩,
⟨.mixed,232,1,18,false,464,550⟩,
⟨.mixed,232,1,19,false,465,167⟩,
⟨.mixed,233,0,(-1),false,45,744⟩,
⟨.mixed,234,0,(-1),false,44,762⟩,
⟨.mixed,234,1,(-1),false,43,762⟩,
⟨.mixed,235,0,0,false,74,70⟩,
⟨.mixed,235,0,1,false,70,70⟩,
⟨.mixed,235,0,2,false,58,26⟩,
⟨.mixed,235,0,3,false,66,556⟩,
⟨.mixed,235,0,4,false,68,173⟩,
⟨.mixed,235,0,5,false,50,74⟩,
⟨.mixed,235,0,6,false,49,74⟩,
⟨.mixed,235,0,7,false,46,30⟩,
⟨.mixed,235,0,8,false,47,560⟩,
⟨.mixed,235,0,9,false,48,177⟩,
⟨.mixed,235,0,10,false,72,312⟩,
⟨.mixed,235,0,11,false,64,312⟩,
⟨.mixed,235,0,12,false,56,16⟩,
⟨.mixed,235,0,13,false,60,546⟩,
⟨.mixed,235,0,14,false,61,163⟩,
⟨.mixed,235,0,15,false,73,58⟩,
⟨.mixed,235,0,16,false,65,58⟩,
⟨.mixed,235,0,17,false,57,20⟩,
⟨.mixed,235,0,18,false,62,550⟩,
⟨.mixed,235,0,19,false,63,167⟩,
⟨.mixed,236,0,(-1),false,415,744⟩,
⟨.mixed,236,1,(-1),false,410,744⟩,
⟨.mixed,236,2,(-1),false,416,744⟩,
⟨.mixed,237,0,(-1),false,377,606⟩,
⟨.mixed,237,1,(-1),false,373,606⟩,
⟨.mixed,237,2,(-1),false,376,606⟩,
⟨.mixed,237,3,(-1),false,372,606⟩,
⟨.mixed,237,4,(-1),false,378,606⟩,
⟨.mixed,237,5,(-1),false,374,606⟩,
⟨.mixed,238,0,(-1),false,381,642⟩,
⟨.mixed,238,1,(-1),false,380,642⟩,
⟨.mixed,238,2,(-1),false,382,642⟩,
⟨.mixed,239,0,(-1),false,412,762⟩,
⟨.mixed,240,0,(-1),false,317,600⟩,
⟨.mixed,241,0,(-1),false,315,618⟩,
⟨.mixed,241,1,(-1),false,313,618⟩,
⟨.mixed,242,0,(-1),false,319,666⟩,
⟨.mixed,243,0,(-1),false,33,744⟩,
⟨.mixed,244,0,(-1),false,32,762⟩,
⟨.mixed,244,1,(-1),false,31,762⟩,
⟨.mixed,245,0,(-1),false,35,52⟩,
⟨.mixed,246,0,(-1),false,379,606⟩,
⟨.mixed,246,1,(-1),false,375,606⟩,
⟨.mixed,247,0,(-1),false,383,642⟩,
⟨.mixed,248,0,(-1),false,417,744⟩,
⟨.mixed,249,0,(-1),false,318,600⟩,
⟨.mixed,250,0,(-1),false,316,618⟩,
⟨.mixed,250,1,(-1),false,314,618⟩,
⟨.mixed,251,0,(-1),false,320,666⟩,
⟨.mixed,252,0,(-1),false,413,1040⟩,
⟨.mixed,253,0,(-1),false,167,624⟩,
⟨.mixed,254,0,(-1),false,166,654⟩,
⟨.mixed,254,1,(-1),false,165,654⟩,
⟨.mixed,255,0,(-1),false,169,696⟩,
⟨.mixed,256,0,(-1),false,414,52⟩,
⟨.mixed,257,0,(-1),false,9,201⟩,
⟨.mixed,258,0,(-1),false,8,207⟩,
⟨.mixed,258,1,(-1),false,7,207⟩,
⟨.mixed,259,0,(-1),false,11,219⟩,
⟨.mixed,260,0,(-1),false,517,294⟩,
⟨.mixed,261,0,(-1),false,223,1074⟩,
⟨.mixed,262,0,(-1),false,231,1086⟩,
⟨.mixed,262,1,(-1),false,229,1086⟩,
⟨.mixed,263,0,(-1),false,235,1110⟩,
⟨.mixed,264,0,(-1),false,120,1080⟩,
⟨.mixed,265,0,(-1),false,132,1098⟩,
⟨.mixed,265,1,(-1),false,129,1098⟩,
⟨.mixed,266,0,(-1),false,157,1122⟩,
⟨.mixed,267,0,(-1),false,342,586⟩,
⟨.mixed,268,0,(-1),false,341,598⟩,
⟨.mixed,268,1,(-1),false,340,598⟩,
⟨.mixed,269,0,(-1),false,343,634⟩,
⟨.mixed,270,0,(-1),false,435,1015⟩,
⟨.mixed,271,0,(-1),false,224,652⟩,
⟨.mixed,272,0,(-1),false,232,694⟩,
⟨.mixed,272,1,(-1),false,230,694⟩,
⟨.mixed,273,0,(-1),false,236,754⟩,
⟨.mixed,274,0,(-1),false,276,592⟩,
⟨.mixed,274,1,(-1),false,274,592⟩,
⟨.mixed,274,2,(-1),false,275,592⟩,
⟨.mixed,274,3,(-1),false,273,592⟩,
⟨.mixed,275,0,(-1),false,272,616⟩,
⟨.mixed,275,1,(-1),false,268,616⟩,
⟨.mixed,275,2,(-1),false,270,616⟩,
⟨.mixed,275,3,(-1),false,266,616⟩,
⟨.mixed,275,4,(-1),false,271,616⟩,
⟨.mixed,275,5,(-1),false,267,616⟩,
⟨.mixed,275,6,(-1),false,269,616⟩,
⟨.mixed,275,7,(-1),false,265,616⟩,
⟨.mixed,276,0,(-1),false,280,664⟩,
⟨.mixed,276,1,(-1),false,278,664⟩,
⟨.mixed,276,2,(-1),false,279,664⟩,
⟨.mixed,276,3,(-1),false,277,664⟩,
⟨.mixed,277,0,(-1),false,439,1032⟩,
⟨.mixed,277,1,(-1),false,437,724⟩,
⟨.mixed,277,2,(-1),false,438,1032⟩,
⟨.mixed,277,3,(-1),false,436,724⟩,
⟨.mixed,278,0,(-1),false,121,688⟩,
⟨.mixed,278,1,(-1),false,119,688⟩,
⟨.mixed,279,0,(-1),false,133,730⟩,
⟨.mixed,279,1,(-1),false,130,730⟩,
⟨.mixed,279,2,(-1),false,131,730⟩,
⟨.mixed,279,3,(-1),false,128,730⟩,
⟨.mixed,280,0,(-1),false,158,778⟩,
⟨.mixed,280,1,(-1),false,156,778⟩,
⟨.mixed,281,0,(-1),false,188,628⟩,
⟨.mixed,281,1,(-1),false,187,82⟩,
⟨.mixed,282,0,(-1),false,186,658⟩,
⟨.mixed,282,1,(-1),false,184,658⟩,
⟨.mixed,282,2,(-1),false,185,88⟩,
⟨.mixed,282,3,(-1),false,183,88⟩,
⟨.mixed,283,0,(-1),false,192,700⟩,
⟨.mixed,283,1,(-1),false,191,94⟩,
⟨.mixed,284,0,0,false,493,62⟩,
⟨.mixed,284,0,1,false,485,62⟩,
⟨.mixed,284,0,2,false,461,24⟩,
⟨.mixed,284,0,3,false,481,554⟩,
⟨.mixed,284,0,4,false,483,171⟩,
⟨.mixed,284,1,0,false,491,115⟩,
⟨.mixed,284,1,1,false,479,115⟩,
⟨.mixed,284,1,2,false,459,24⟩,
⟨.mixed,284,1,3,false,475,554⟩,
⟨.mixed,284,1,4,false,477,171⟩,
⟨.mixed,285,0,(-1),false,45,748⟩,
⟨.mixed,286,0,(-1),false,44,766⟩,
⟨.mixed,286,1,(-1),false,43,766⟩,
⟨.mixed,287,0,0,false,75,62⟩,
⟨.mixed,287,0,1,false,71,62⟩,
⟨.mixed,287,0,2,false,59,24⟩,
⟨.mixed,287,0,3,false,67,554⟩,
⟨.mixed,287,0,4,false,69,171⟩,
⟨.mixed,288,0,(-1),false,415,748⟩,
⟨.mixed,288,1,(-1),false,410,748⟩,
⟨.mixed,288,2,(-1),false,416,748⟩,
⟨.mixed,289,0,(-1),false,377,610⟩,
⟨.mixed,289,1,(-1),false,373,610⟩,
⟨.mixed,289,2,(-1),false,376,610⟩,
⟨.mixed,289,3,(-1),false,372,610⟩,
⟨.mixed,289,4,(-1),false,378,610⟩,
⟨.mixed,289,5,(-1),false,374,610⟩,
⟨.mixed,290,0,(-1),false,381,646⟩,
⟨.mixed,290,1,(-1),false,380,646⟩,
⟨.mixed,290,2,(-1),false,382,646⟩,
⟨.mixed,291,0,(-1),false,412,766⟩,
⟨.mixed,292,0,(-1),false,317,604⟩,
⟨.mixed,293,0,(-1),false,315,622⟩,
⟨.mixed,293,1,(-1),false,313,622⟩,
⟨.mixed,294,0,(-1),false,319,670⟩,
⟨.mixed,295,0,(-1),false,33,748⟩,
⟨.mixed,296,0,(-1),false,32,766⟩,
⟨.mixed,296,1,(-1),false,31,766⟩,
⟨.mixed,297,0,(-1),false,35,56⟩,
⟨.mixed,298,0,(-1),false,379,610⟩,
⟨.mixed,298,1,(-1),false,375,610⟩,
⟨.mixed,299,0,(-1),false,383,646⟩,
⟨.mixed,300,0,(-1),false,417,748⟩,
⟨.mixed,301,0,(-1),false,318,604⟩,
⟨.mixed,302,0,(-1),false,316,622⟩,
⟨.mixed,302,1,(-1),false,314,622⟩,
⟨.mixed,303,0,(-1),false,320,670⟩,
⟨.mixed,304,0,(-1),false,413,1044⟩,
⟨.mixed,305,0,(-1),false,167,628⟩,
⟨.mixed,306,0,(-1),false,166,658⟩,
⟨.mixed,306,1,(-1),false,165,658⟩,
⟨.mixed,307,0,(-1),false,169,700⟩,
⟨.mixed,308,0,(-1),false,414,56⟩,
⟨.mixed,309,0,(-1),false,9,205⟩,
⟨.mixed,310,0,(-1),false,8,211⟩,
⟨.mixed,310,1,(-1),false,7,211⟩,
⟨.mixed,311,0,(-1),false,11,221⟩,
⟨.mixed,312,0,(-1),false,517,298⟩
] := by rfl
end M7ContinueSep17.CatalogueGeneral

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def recs756 : List LowerHistoryRecord := [⟨.mixed,72,0,(-1),false,158,775⟩,⟨.mixed,72,1,(-1),false,156,775⟩]
theorem records756 : lowerHistoryRecordsFor (⟨.mixed,72,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),true)],([2,2,2,1],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs756 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 72)) = recs756
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs757 : List LowerHistoryRecord := [⟨.mixed,73,0,(-1),false,188,625⟩,⟨.mixed,73,1,(-1),false,187,79⟩]
theorem records757 : lowerHistoryRecordsFor (⟨.mixed,73,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([2,2,1,1,1,3],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs757 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 73)) = recs757
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs758 : List LowerHistoryRecord := [⟨.mixed,74,0,(-1),false,186,655⟩,⟨.mixed,74,1,(-1),false,184,655⟩,⟨.mixed,74,2,(-1),false,185,85⟩,⟨.mixed,74,3,(-1),false,183,85⟩]
theorem records758 : lowerHistoryRecordsFor (⟨.mixed,74,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([2,2,1,1,1,2],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩ : LowerHistoryPath) = recs758 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 74)) = recs758
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs759 : List LowerHistoryRecord := [⟨.mixed,75,0,(-1),false,192,697⟩,⟨.mixed,75,1,(-1),false,191,91⟩]
theorem records759 : lowerHistoryRecordsFor (⟨.mixed,75,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([2,2,1,1,1,1],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs759 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 75)) = recs759
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs760 : List LowerHistoryRecord := [⟨.mixed,76,0,0,false,492,71⟩,⟨.mixed,76,0,1,false,484,71⟩,⟨.mixed,76,0,2,false,460,27⟩,⟨.mixed,76,0,3,false,480,557⟩,⟨.mixed,76,0,4,false,482,174⟩,⟨.mixed,76,0,5,false,449,75⟩,⟨.mixed,76,0,6,false,447,75⟩,⟨.mixed,76,0,7,false,441,31⟩,⟨.mixed,76,0,8,false,445,561⟩,⟨.mixed,76,0,9,false,446,178⟩,⟨.mixed,76,0,10,false,488,313⟩,⟨.mixed,76,0,11,false,472,313⟩,⟨.mixed,76,0,12,false,456,17⟩,⟨.mixed,76,0,13,false,468,547⟩,⟨.mixed,76,0,14,false,469,164⟩,⟨.mixed,76,0,15,false,489,59⟩,⟨.mixed,76,0,16,false,473,59⟩,⟨.mixed,76,0,17,false,457,21⟩,⟨.mixed,76,0,18,false,470,551⟩,⟨.mixed,76,0,19,false,471,168⟩,⟨.mixed,76,1,0,false,490,154⟩,⟨.mixed,76,1,1,false,478,154⟩,⟨.mixed,76,1,2,false,458,27⟩,⟨.mixed,76,1,3,false,474,557⟩,⟨.mixed,76,1,4,false,476,174⟩,⟨.mixed,76,1,5,false,448,158⟩,⟨.mixed,76,1,6,false,444,158⟩,⟨.mixed,76,1,7,false,440,31⟩,⟨.mixed,76,1,8,false,442,561⟩,⟨.mixed,76,1,9,false,443,178⟩,⟨.mixed,76,1,10,false,486,109⟩,⟨.mixed,76,1,11,false,466,109⟩,⟨.mixed,76,1,12,false,454,17⟩,⟨.mixed,76,1,13,false,462,547⟩,⟨.mixed,76,1,14,false,463,164⟩,⟨.mixed,76,1,15,false,487,112⟩,⟨.mixed,76,1,16,false,467,112⟩,⟨.mixed,76,1,17,false,455,21⟩,⟨.mixed,76,1,18,false,464,551⟩,⟨.mixed,76,1,19,false,465,168⟩]
theorem records760 : lowerHistoryRecordsFor (⟨.mixed,76,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false)],([2,2,1,1],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs760 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 76)) = recs760
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
end M7ContinueSep17.Noninitial20260918.B755_760

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
namespace M7ContinueSep17.Noninitial20260918.B755_760
theorem premise156 : lowerHistoryPremises[155]? = some ([3,5,21,256,260,265,275,371,420,440,780,801,815,817,843,856,876] : List Nat) := by
  have hg : lowerHistoryPremises[155]? = lowerHistoryPremises01[155]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 155 (by decide)
  exact hg.trans (by rfl)
theorem premise158 : lowerHistoryPremises[157]? = some ([3,5,21,256,260,265,371,420,440,780,801,815,817,843,856,1153] : List Nat) := by
  have hg : lowerHistoryPremises[157]? = lowerHistoryPremises01[157]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 157 (by decide)
  exact hg.trans (by rfl)
theorem premise183 : lowerHistoryPremises[182]? = some ([3,6,13,21,185,215,220,260,282,287,371,396,419,440,653,706,769,784,810,811,837,843,852,856,869,1181] : List Nat) := by
  have hg : lowerHistoryPremises[182]? = lowerHistoryPremises01[182]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 182 (by decide)
  exact hg.trans (by rfl)
theorem premise184 : lowerHistoryPremises[183]? = some ([3,6,13,21,185,215,220,260,282,371,396,419,440,653,706,769,784,810,837,843,856,869,1165] : List Nat) := by
  have hg : lowerHistoryPremises[183]? = lowerHistoryPremises01[183]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 183 (by decide)
  exact hg.trans (by rfl)
theorem premise185 : lowerHistoryPremises[184]? = some ([3,6,13,21,185,215,260,282,287,371,396,419,440,653,706,769,784,810,811,837,843,852,856,1078,1181] : List Nat) := by
  have hg : lowerHistoryPremises[184]? = lowerHistoryPremises01[184]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 184 (by decide)
  exact hg.trans (by rfl)
theorem premise186 : lowerHistoryPremises[185]? = some ([3,6,13,21,185,215,260,282,371,396,419,440,653,706,769,784,810,837,843,856,1078,1165] : List Nat) := by
  have hg : lowerHistoryPremises[185]? = lowerHistoryPremises01[185]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 185 (by decide)
  exact hg.trans (by rfl)
theorem premise187 : lowerHistoryPremises[186]? = some ([3,6,13,21,193,206,260,282,287,371,403,419,440,609,661,769,784,810,811,837,843,852,856,1078,1181] : List Nat) := by
  have hg : lowerHistoryPremises[186]? = lowerHistoryPremises01[186]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 186 (by decide)
  exact hg.trans (by rfl)
theorem premise188 : lowerHistoryPremises[187]? = some ([3,6,13,21,193,206,260,282,371,403,419,440,609,661,769,784,810,837,843,856,1078,1165] : List Nat) := by
  have hg : lowerHistoryPremises[187]? = lowerHistoryPremises01[187]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 187 (by decide)
  exact hg.trans (by rfl)
theorem premise191 : lowerHistoryPremises[190]? = some ([3,6,13,21,219,237,260,282,287,371,419,440,728,761,769,784,810,811,837,843,852,856,1181] : List Nat) := by
  have hg : lowerHistoryPremises[190]? = lowerHistoryPremises01[190]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 190 (by decide)
  exact hg.trans (by rfl)
theorem premise192 : lowerHistoryPremises[191]? = some ([3,6,13,21,219,237,260,282,371,419,440,728,761,769,784,810,837,843,856,1165] : List Nat) := by
  have hg : lowerHistoryPremises[191]? = lowerHistoryPremises01[191]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 191 (by decide)
  exact hg.trans (by rfl)
theorem premise440 : lowerHistoryPremises[439]? = some ([3,21,259,260,270,278,279,282,286,287,371,419,440,784,811,831,836,837,843,846,848,852,856,1171,1181] : List Nat) := by
  have hg : lowerHistoryPremises[439]? = lowerHistoryPremises03[39]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 39 (by decide)
  exact hg.trans (by rfl)
theorem premise441 : lowerHistoryPremises[440]? = some ([3,21,259,260,270,278,279,282,286,371,419,440,784,831,836,837,843,846,848,856,1165,1171] : List Nat) := by
  have hg : lowerHistoryPremises[440]? = lowerHistoryPremises03[40]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 40 (by decide)
  exact hg.trans (by rfl)
theorem premise442 : lowerHistoryPremises[441]? = some ([3,21,259,260,270,279,282,286,287,290,371,419,437,440,784,811,831,836,837,843,846,852,856,1172,1181] : List Nat) := by
  have hg : lowerHistoryPremises[441]? = lowerHistoryPremises03[41]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 41 (by decide)
  exact hg.trans (by rfl)
theorem premise443 : lowerHistoryPremises[442]? = some ([3,21,259,260,270,279,282,286,287,290,371,419,440,784,811,831,836,837,843,846,849,852,856,1170,1181] : List Nat) := by
  have hg : lowerHistoryPremises[442]? = lowerHistoryPremises03[42]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 42 (by decide)
  exact hg.trans (by rfl)
theorem premise444 : lowerHistoryPremises[443]? = some ([3,21,259,260,270,279,282,286,287,371,419,440,784,811,831,836,837,843,846,848,852,856,1159,1172,1181] : List Nat) := by
  have hg : lowerHistoryPremises[443]? = lowerHistoryPremises03[43]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 43 (by decide)
  exact hg.trans (by rfl)
theorem premise445 : lowerHistoryPremises[444]? = some ([3,21,259,260,270,279,282,286,290,371,419,437,440,784,831,836,837,843,846,856,1165,1172] : List Nat) := by
  have hg : lowerHistoryPremises[444]? = lowerHistoryPremises03[44]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 44 (by decide)
  exact hg.trans (by rfl)
theorem premise446 : lowerHistoryPremises[445]? = some ([3,21,259,260,270,279,282,286,290,371,419,440,784,831,836,837,843,846,849,856,1165,1170] : List Nat) := by
  have hg : lowerHistoryPremises[445]? = lowerHistoryPremises03[45]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 45 (by decide)
  exact hg.trans (by rfl)
theorem premise447 : lowerHistoryPremises[446]? = some ([3,21,259,260,270,279,282,286,371,419,440,784,831,836,837,843,846,848,856,1159,1165,1172] : List Nat) := by
  have hg : lowerHistoryPremises[446]? = lowerHistoryPremises03[46]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 46 (by decide)
  exact hg.trans (by rfl)
theorem premise448 : lowerHistoryPremises[447]? = some ([3,21,259,260,270,282,286,287,371,419,440,784,811,828,831,836,837,843,846,852,856,1172,1181] : List Nat) := by
  have hg : lowerHistoryPremises[447]? = lowerHistoryPremises03[47]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 47 (by decide)
  exact hg.trans (by rfl)
theorem premise449 : lowerHistoryPremises[448]? = some ([3,21,259,260,270,282,286,371,419,440,784,828,831,836,837,843,846,856,1165,1172] : List Nat) := by
  have hg : lowerHistoryPremises[448]? = lowerHistoryPremises03[48]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 48 (by decide)
  exact hg.trans (by rfl)
theorem premise454 : lowerHistoryPremises[453]? = some ([3,21,260,270,278,279,282,284,286,287,371,419,429,440,784,811,831,837,843,846,848,852,856,882,1181] : List Nat) := by
  have hg : lowerHistoryPremises[453]? = lowerHistoryPremises03[53]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 53 (by decide)
  exact hg.trans (by rfl)
theorem premise455 : lowerHistoryPremises[454]? = some ([3,21,260,270,278,279,282,284,286,287,371,419,440,784,811,819,831,837,843,846,848,852,856,897,1181] : List Nat) := by
  have hg : lowerHistoryPremises[454]? = lowerHistoryPremises03[54]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 54 (by decide)
  exact hg.trans (by rfl)
theorem premise456 : lowerHistoryPremises[455]? = some ([3,21,260,270,278,279,282,284,286,371,419,429,440,784,831,837,843,846,848,856,882,1165] : List Nat) := by
  have hg : lowerHistoryPremises[455]? = lowerHistoryPremises03[55]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 55 (by decide)
  exact hg.trans (by rfl)
theorem premise457 : lowerHistoryPremises[456]? = some ([3,21,260,270,278,279,282,284,286,371,419,440,784,819,831,837,843,846,848,856,897,1165] : List Nat) := by
  have hg : lowerHistoryPremises[456]? = lowerHistoryPremises03[56]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 56 (by decide)
  exact hg.trans (by rfl)
theorem premise458 : lowerHistoryPremises[457]? = some ([3,21,260,270,278,279,282,286,287,371,419,440,784,811,831,836,837,843,846,848,852,856,882,1139,1181] : List Nat) := by
  have hg : lowerHistoryPremises[457]? = lowerHistoryPremises03[57]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 57 (by decide)
  exact hg.trans (by rfl)
theorem premise460 : lowerHistoryPremises[459]? = some ([3,21,260,270,278,279,282,286,371,419,440,784,831,836,837,843,846,848,856,882,1139,1165] : List Nat) := by
  have hg : lowerHistoryPremises[459]? = lowerHistoryPremises03[59]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 59 (by decide)
  exact hg.trans (by rfl)
theorem premise462 : lowerHistoryPremises[461]? = some ([3,21,260,270,279,282,284,286,287,290,371,419,429,437,440,784,811,831,837,843,846,852,856,886,1181] : List Nat) := by
  have hg : lowerHistoryPremises[461]? = lowerHistoryPremises03[61]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 61 (by decide)
  exact hg.trans (by rfl)
theorem premise463 : lowerHistoryPremises[462]? = some ([3,21,260,270,279,282,284,286,287,290,371,419,429,440,784,811,831,837,843,846,849,852,856,888,1181] : List Nat) := by
  have hg : lowerHistoryPremises[462]? = lowerHistoryPremises03[62]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 62 (by decide)
  exact hg.trans (by rfl)
theorem premise464 : lowerHistoryPremises[463]? = some ([3,21,260,270,279,282,284,286,287,290,371,419,437,440,784,811,819,831,837,843,846,852,856,898,1181] : List Nat) := by
  have hg : lowerHistoryPremises[463]? = lowerHistoryPremises03[63]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 63 (by decide)
  exact hg.trans (by rfl)
theorem premise465 : lowerHistoryPremises[464]? = some ([3,21,260,270,279,282,284,286,287,290,371,419,440,784,811,819,831,837,843,846,849,852,856,899,1181] : List Nat) := by
  have hg : lowerHistoryPremises[464]? = lowerHistoryPremises03[64]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 64 (by decide)
  exact hg.trans (by rfl)
theorem premise466 : lowerHistoryPremises[465]? = some ([3,21,260,270,279,282,284,286,287,371,419,429,440,784,811,831,837,843,846,848,852,856,886,1159,1181] : List Nat) := by
  have hg : lowerHistoryPremises[465]? = lowerHistoryPremises03[65]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 65 (by decide)
  exact hg.trans (by rfl)
theorem premise467 : lowerHistoryPremises[466]? = some ([3,21,260,270,279,282,284,286,287,371,419,440,784,811,819,831,837,843,846,848,852,856,898,1159,1181] : List Nat) := by
  have hg : lowerHistoryPremises[466]? = lowerHistoryPremises03[66]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 66 (by decide)
  exact hg.trans (by rfl)
theorem premise468 : lowerHistoryPremises[467]? = some ([3,21,260,270,279,282,284,286,290,371,419,429,437,440,784,831,837,843,846,856,886,1165] : List Nat) := by
  have hg : lowerHistoryPremises[467]? = lowerHistoryPremises03[67]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 67 (by decide)
  exact hg.trans (by rfl)
theorem premise469 : lowerHistoryPremises[468]? = some ([3,21,260,270,279,282,284,286,290,371,419,429,440,784,831,837,843,846,849,856,888,1165] : List Nat) := by
  have hg : lowerHistoryPremises[468]? = lowerHistoryPremises03[68]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 68 (by decide)
  exact hg.trans (by rfl)
theorem premise470 : lowerHistoryPremises[469]? = some ([3,21,260,270,279,282,284,286,290,371,419,437,440,784,819,831,837,843,846,856,898,1165] : List Nat) := by
  have hg : lowerHistoryPremises[469]? = lowerHistoryPremises03[69]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 69 (by decide)
  exact hg.trans (by rfl)
theorem premise471 : lowerHistoryPremises[470]? = some ([3,21,260,270,279,282,284,286,290,371,419,440,784,819,831,837,843,846,849,856,899,1165] : List Nat) := by
  have hg : lowerHistoryPremises[470]? = lowerHistoryPremises03[70]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 70 (by decide)
  exact hg.trans (by rfl)
theorem premise472 : lowerHistoryPremises[471]? = some ([3,21,260,270,279,282,284,286,371,419,429,440,784,831,837,843,846,848,856,886,1159,1165] : List Nat) := by
  have hg : lowerHistoryPremises[471]? = lowerHistoryPremises03[71]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 71 (by decide)
  exact hg.trans (by rfl)
theorem premise473 : lowerHistoryPremises[472]? = some ([3,21,260,270,279,282,284,286,371,419,440,784,819,831,837,843,846,848,856,898,1159,1165] : List Nat) := by
  have hg : lowerHistoryPremises[472]? = lowerHistoryPremises03[72]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 72 (by decide)
  exact hg.trans (by rfl)
theorem premise474 : lowerHistoryPremises[473]? = some ([3,21,260,270,279,282,286,287,290,371,419,437,440,784,811,831,836,837,843,846,852,856,886,1139,1181] : List Nat) := by
  have hg : lowerHistoryPremises[473]? = lowerHistoryPremises03[73]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 73 (by decide)
  exact hg.trans (by rfl)
theorem premise476 : lowerHistoryPremises[475]? = some ([3,21,260,270,279,282,286,287,290,371,419,440,784,811,831,836,837,843,846,849,852,856,888,1139,1181] : List Nat) := by
  have hg : lowerHistoryPremises[475]? = lowerHistoryPremises03[75]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 75 (by decide)
  exact hg.trans (by rfl)
theorem premise478 : lowerHistoryPremises[477]? = some ([3,21,260,270,279,282,286,287,371,419,440,784,811,831,836,837,843,846,848,852,856,886,1139,1159,1181] : List Nat) := by
  have hg : lowerHistoryPremises[477]? = lowerHistoryPremises03[77]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 77 (by decide)
  exact hg.trans (by rfl)
theorem premise480 : lowerHistoryPremises[479]? = some ([3,21,260,270,279,282,286,290,371,419,437,440,784,831,836,837,843,846,856,886,1139,1165] : List Nat) := by
  have hg : lowerHistoryPremises[479]? = lowerHistoryPremises03[79]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 79 (by decide)
  exact hg.trans (by rfl)
theorem premise482 : lowerHistoryPremises[481]? = some ([3,21,260,270,279,282,286,290,371,419,440,784,831,836,837,843,846,849,856,888,1139,1165] : List Nat) := by
  have hg : lowerHistoryPremises[481]? = lowerHistoryPremises03[81]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 81 (by decide)
  exact hg.trans (by rfl)
theorem premise484 : lowerHistoryPremises[483]? = some ([3,21,260,270,279,282,286,371,419,440,784,831,836,837,843,846,848,856,886,1139,1159,1165] : List Nat) := by
  have hg : lowerHistoryPremises[483]? = lowerHistoryPremises03[83]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 83 (by decide)
  exact hg.trans (by rfl)
theorem premise486 : lowerHistoryPremises[485]? = some ([3,21,260,270,282,284,286,287,371,419,429,440,784,811,828,831,837,843,846,852,856,886,1181] : List Nat) := by
  have hg : lowerHistoryPremises[485]? = lowerHistoryPremises03[85]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 85 (by decide)
  exact hg.trans (by rfl)
theorem premise487 : lowerHistoryPremises[486]? = some ([3,21,260,270,282,284,286,287,371,419,440,784,811,819,828,831,837,843,846,852,856,898,1181] : List Nat) := by
  have hg : lowerHistoryPremises[486]? = lowerHistoryPremises03[86]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 86 (by decide)
  exact hg.trans (by rfl)
theorem premise488 : lowerHistoryPremises[487]? = some ([3,21,260,270,282,284,286,371,419,429,440,784,828,831,837,843,846,856,886,1165] : List Nat) := by
  have hg : lowerHistoryPremises[487]? = lowerHistoryPremises03[87]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 87 (by decide)
  exact hg.trans (by rfl)
theorem premise489 : lowerHistoryPremises[488]? = some ([3,21,260,270,282,284,286,371,419,440,784,819,828,831,837,843,846,856,898,1165] : List Nat) := by
  have hg : lowerHistoryPremises[488]? = lowerHistoryPremises03[88]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 88 (by decide)
  exact hg.trans (by rfl)
theorem premise490 : lowerHistoryPremises[489]? = some ([3,21,260,270,282,286,287,371,419,440,784,811,828,831,836,837,843,846,852,856,886,1139,1181] : List Nat) := by
  have hg : lowerHistoryPremises[489]? = lowerHistoryPremises03[89]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 89 (by decide)
  exact hg.trans (by rfl)
theorem premise492 : lowerHistoryPremises[491]? = some ([3,21,260,270,282,286,371,419,440,784,828,831,836,837,843,846,856,886,1139,1165] : List Nat) := by
  have hg : lowerHistoryPremises[491]? = lowerHistoryPremises03[91]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 91 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Noninitial20260918.B755_760
theorem witness17_projection : (lowerHistoryWitness 17).lowerBound = lowerHistoryBound 278 ∧ (lowerHistoryWitness 17).upperBound = lowerHistoryBound 882 ∧ (lowerHistoryWitness 17).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[16]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 278, lowerHistoryBound 882, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 278, lowerHistoryBound 882, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[16]? = lowerHistoryWitnesses01[16]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 16 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness21_projection : (lowerHistoryWitness 21).lowerBound = lowerHistoryBound 278 ∧ (lowerHistoryWitness 21).upperBound = lowerHistoryBound 897 ∧ (lowerHistoryWitness 21).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[20]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 278, lowerHistoryBound 897, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 278, lowerHistoryBound 897, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[20]? = lowerHistoryWitnesses01[20]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 20 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness27_projection : (lowerHistoryWitness 27).lowerBound = lowerHistoryBound 278 ∧ (lowerHistoryWitness 27).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 27).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[26]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 278, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 278, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[26]? = lowerHistoryWitnesses01[26]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 26 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness31_projection : (lowerHistoryWitness 31).lowerBound = lowerHistoryBound 278 ∧ (lowerHistoryWitness 31).upperBound = lowerHistoryBound 1171 ∧ (lowerHistoryWitness 31).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[30]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 278, lowerHistoryBound 1171, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 278, lowerHistoryBound 1171, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[30]? = lowerHistoryWitnesses01[30]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 30 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness59_projection : (lowerHistoryWitness 59).lowerBound = lowerHistoryBound 286 ∧ (lowerHistoryWitness 59).upperBound = lowerHistoryBound 898 ∧ (lowerHistoryWitness 59).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[58]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 286, lowerHistoryBound 898, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 286, lowerHistoryBound 898, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[58]? = lowerHistoryWitnesses01[58]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 58 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness71_projection : (lowerHistoryWitness 71).lowerBound = lowerHistoryBound 286 ∧ (lowerHistoryWitness 71).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 71).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[70]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 286, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 286, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[70]? = lowerHistoryWitnesses01[70]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 70 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness75_projection : (lowerHistoryWitness 75).lowerBound = lowerHistoryBound 286 ∧ (lowerHistoryWitness 75).upperBound = lowerHistoryBound 1172 ∧ (lowerHistoryWitness 75).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[74]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 286, lowerHistoryBound 1172, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 286, lowerHistoryBound 1172, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[74]? = lowerHistoryWitnesses01[74]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 74 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness79_projection : (lowerHistoryWitness 79).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 79).upperBound = lowerHistoryBound 661 ∧ (lowerHistoryWitness 79).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[78]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 661, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 661, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[78]? = lowerHistoryWitnesses01[78]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 78 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness85_projection : (lowerHistoryWitness 85).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 85).upperBound = lowerHistoryBound 706 ∧ (lowerHistoryWitness 85).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[84]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 706, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 706, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[84]? = lowerHistoryWitnesses01[84]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 84 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness91_projection : (lowerHistoryWitness 91).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 91).upperBound = lowerHistoryBound 761 ∧ (lowerHistoryWitness 91).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[90]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 761, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 761, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[90]? = lowerHistoryWitnesses01[90]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 90 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness109_projection : (lowerHistoryWitness 109).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 109).upperBound = lowerHistoryBound 886 ∧ (lowerHistoryWitness 109).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[108]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 886, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 886, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[108]? = lowerHistoryWitnesses01[108]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 108 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness112_projection : (lowerHistoryWitness 112).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 112).upperBound = lowerHistoryBound 898 ∧ (lowerHistoryWitness 112).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[111]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 898, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 898, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[111]? = lowerHistoryWitnesses01[111]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 111 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness154_projection : (lowerHistoryWitness 154).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 154).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 154).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[153]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[153]? = lowerHistoryWitnesses01[153]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 153 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness158_projection : (lowerHistoryWitness 158).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 158).upperBound = lowerHistoryBound 1172 ∧ (lowerHistoryWitness 158).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[157]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 1172, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 1172, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[157]? = lowerHistoryWitnesses01[157]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 157 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness164_projection : (lowerHistoryWitness 164).lowerBound = lowerHistoryBound 290 ∧ (lowerHistoryWitness 164).upperBound = lowerHistoryBound 888 ∧ (lowerHistoryWitness 164).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[163]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 290, lowerHistoryBound 888, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 290, lowerHistoryBound 888, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[163]? = lowerHistoryWitnesses01[163]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 163 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness168_projection : (lowerHistoryWitness 168).lowerBound = lowerHistoryBound 290 ∧ (lowerHistoryWitness 168).upperBound = lowerHistoryBound 899 ∧ (lowerHistoryWitness 168).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[167]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 290, lowerHistoryBound 899, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 290, lowerHistoryBound 899, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[167]? = lowerHistoryWitnesses01[167]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 167 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness174_projection : (lowerHistoryWitness 174).lowerBound = lowerHistoryBound 290 ∧ (lowerHistoryWitness 174).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 174).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[173]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 290, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 290, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[173]? = lowerHistoryWitnesses01[173]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 173 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness178_projection : (lowerHistoryWitness 178).lowerBound = lowerHistoryBound 290 ∧ (lowerHistoryWitness 178).upperBound = lowerHistoryBound 1170 ∧ (lowerHistoryWitness 178).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[177]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 290, lowerHistoryBound 1170, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 290, lowerHistoryBound 1170, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[177]? = lowerHistoryWitnesses01[177]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 177 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness313_projection : (lowerHistoryWitness 313).lowerBound = lowerHistoryBound 429 ∧ (lowerHistoryWitness 313).upperBound = lowerHistoryBound 886 ∧ (lowerHistoryWitness 313).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[112]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 429, lowerHistoryBound 886, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 429, lowerHistoryBound 886, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[312]? = lowerHistoryWitnesses02[112]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 112 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness547_projection : (lowerHistoryWitness 547).lowerBound = lowerHistoryBound 437 ∧ (lowerHistoryWitness 547).upperBound = lowerHistoryBound 886 ∧ (lowerHistoryWitness 547).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[146]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 437, lowerHistoryBound 886, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 437, lowerHistoryBound 886, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[546]? = lowerHistoryWitnesses03[146]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 146 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness551_projection : (lowerHistoryWitness 551).lowerBound = lowerHistoryBound 437 ∧ (lowerHistoryWitness 551).upperBound = lowerHistoryBound 898 ∧ (lowerHistoryWitness 551).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[150]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 437, lowerHistoryBound 898, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 437, lowerHistoryBound 898, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[550]? = lowerHistoryWitnesses03[150]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 150 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness557_projection : (lowerHistoryWitness 557).lowerBound = lowerHistoryBound 437 ∧ (lowerHistoryWitness 557).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 557).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[156]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 437, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 437, lowerHistoryBound 1139, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[556]? = lowerHistoryWitnesses03[156]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 156 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness561_projection : (lowerHistoryWitness 561).lowerBound = lowerHistoryBound 437 ∧ (lowerHistoryWitness 561).upperBound = lowerHistoryBound 1172 ∧ (lowerHistoryWitness 561).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[160]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 437, lowerHistoryBound 1172, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 437, lowerHistoryBound 1172, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[560]? = lowerHistoryWitnesses03[160]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 160 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness625_projection : (lowerHistoryWitness 625).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 625).upperBound = lowerHistoryBound 661 ∧ (lowerHistoryWitness 625).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[24]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 661, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 661, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[624]? = lowerHistoryWitnesses04[24]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 24 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness655_projection : (lowerHistoryWitness 655).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 655).upperBound = lowerHistoryBound 706 ∧ (lowerHistoryWitness 655).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[54]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 706, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 706, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[654]? = lowerHistoryWitnesses04[54]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 54 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness697_projection : (lowerHistoryWitness 697).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 697).upperBound = lowerHistoryBound 761 ∧ (lowerHistoryWitness 697).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[96]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 761, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 761, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[696]? = lowerHistoryWitnesses04[96]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 96 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness775_projection : (lowerHistoryWitness 775).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 775).upperBound = lowerHistoryBound 815 ∧ (lowerHistoryWitness 775).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[174]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 815, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 815, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[774]? = lowerHistoryWitnesses04[174]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 174 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 17 => (278,882)
  | 21 => (278,897)
  | 27 => (278,1139)
  | 31 => (278,1171)
  | 59 => (286,898)
  | 71 => (286,1139)
  | 75 => (286,1172)
  | 79 => (287,661)
  | 85 => (287,706)
  | 91 => (287,761)
  | 109 => (287,886)
  | 112 => (287,898)
  | 154 => (287,1139)
  | 158 => (287,1172)
  | 164 => (290,888)
  | 168 => (290,899)
  | 174 => (290,1139)
  | 178 => (290,1170)
  | 313 => (429,886)
  | 547 => (437,886)
  | 551 => (437,898)
  | 557 => (437,1139)
  | 561 => (437,1172)
  | 625 => (440,661)
  | 655 => (440,706)
  | 697 => (440,761)
  | 775 => (440,815)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 156 => [3,5,21,256,260,265,275,371,420,440,780,801,815,817,843,856,876]
  | 158 => [3,5,21,256,260,265,371,420,440,780,801,815,817,843,856,1153]
  | 183 => [3,6,13,21,185,215,220,260,282,287,371,396,419,440,653,706,769,784,810,811,837,843,852,856,869,1181]
  | 184 => [3,6,13,21,185,215,220,260,282,371,396,419,440,653,706,769,784,810,837,843,856,869,1165]
  | 185 => [3,6,13,21,185,215,260,282,287,371,396,419,440,653,706,769,784,810,811,837,843,852,856,1078,1181]
  | 186 => [3,6,13,21,185,215,260,282,371,396,419,440,653,706,769,784,810,837,843,856,1078,1165]
  | 187 => [3,6,13,21,193,206,260,282,287,371,403,419,440,609,661,769,784,810,811,837,843,852,856,1078,1181]
  | 188 => [3,6,13,21,193,206,260,282,371,403,419,440,609,661,769,784,810,837,843,856,1078,1165]
  | 191 => [3,6,13,21,219,237,260,282,287,371,419,440,728,761,769,784,810,811,837,843,852,856,1181]
  | 192 => [3,6,13,21,219,237,260,282,371,419,440,728,761,769,784,810,837,843,856,1165]
  | 440 => [3,21,259,260,270,278,279,282,286,287,371,419,440,784,811,831,836,837,843,846,848,852,856,1171,1181]
  | 441 => [3,21,259,260,270,278,279,282,286,371,419,440,784,831,836,837,843,846,848,856,1165,1171]
  | 442 => [3,21,259,260,270,279,282,286,287,290,371,419,437,440,784,811,831,836,837,843,846,852,856,1172,1181]
  | 443 => [3,21,259,260,270,279,282,286,287,290,371,419,440,784,811,831,836,837,843,846,849,852,856,1170,1181]
  | 444 => [3,21,259,260,270,279,282,286,287,371,419,440,784,811,831,836,837,843,846,848,852,856,1159,1172,1181]
  | 445 => [3,21,259,260,270,279,282,286,290,371,419,437,440,784,831,836,837,843,846,856,1165,1172]
  | 446 => [3,21,259,260,270,279,282,286,290,371,419,440,784,831,836,837,843,846,849,856,1165,1170]
  | 447 => [3,21,259,260,270,279,282,286,371,419,440,784,831,836,837,843,846,848,856,1159,1165,1172]
  | 448 => [3,21,259,260,270,282,286,287,371,419,440,784,811,828,831,836,837,843,846,852,856,1172,1181]
  | 449 => [3,21,259,260,270,282,286,371,419,440,784,828,831,836,837,843,846,856,1165,1172]
  | 454 => [3,21,260,270,278,279,282,284,286,287,371,419,429,440,784,811,831,837,843,846,848,852,856,882,1181]
  | 455 => [3,21,260,270,278,279,282,284,286,287,371,419,440,784,811,819,831,837,843,846,848,852,856,897,1181]
  | 456 => [3,21,260,270,278,279,282,284,286,371,419,429,440,784,831,837,843,846,848,856,882,1165]
  | 457 => [3,21,260,270,278,279,282,284,286,371,419,440,784,819,831,837,843,846,848,856,897,1165]
  | 458 => [3,21,260,270,278,279,282,286,287,371,419,440,784,811,831,836,837,843,846,848,852,856,882,1139,1181]
  | 460 => [3,21,260,270,278,279,282,286,371,419,440,784,831,836,837,843,846,848,856,882,1139,1165]
  | 462 => [3,21,260,270,279,282,284,286,287,290,371,419,429,437,440,784,811,831,837,843,846,852,856,886,1181]
  | 463 => [3,21,260,270,279,282,284,286,287,290,371,419,429,440,784,811,831,837,843,846,849,852,856,888,1181]
  | 464 => [3,21,260,270,279,282,284,286,287,290,371,419,437,440,784,811,819,831,837,843,846,852,856,898,1181]
  | 465 => [3,21,260,270,279,282,284,286,287,290,371,419,440,784,811,819,831,837,843,846,849,852,856,899,1181]
  | 466 => [3,21,260,270,279,282,284,286,287,371,419,429,440,784,811,831,837,843,846,848,852,856,886,1159,1181]
  | 467 => [3,21,260,270,279,282,284,286,287,371,419,440,784,811,819,831,837,843,846,848,852,856,898,1159,1181]
  | 468 => [3,21,260,270,279,282,284,286,290,371,419,429,437,440,784,831,837,843,846,856,886,1165]
  | 469 => [3,21,260,270,279,282,284,286,290,371,419,429,440,784,831,837,843,846,849,856,888,1165]
  | 470 => [3,21,260,270,279,282,284,286,290,371,419,437,440,784,819,831,837,843,846,856,898,1165]
  | 471 => [3,21,260,270,279,282,284,286,290,371,419,440,784,819,831,837,843,846,849,856,899,1165]
  | 472 => [3,21,260,270,279,282,284,286,371,419,429,440,784,831,837,843,846,848,856,886,1159,1165]
  | 473 => [3,21,260,270,279,282,284,286,371,419,440,784,819,831,837,843,846,848,856,898,1159,1165]
  | 474 => [3,21,260,270,279,282,286,287,290,371,419,437,440,784,811,831,836,837,843,846,852,856,886,1139,1181]
  | 476 => [3,21,260,270,279,282,286,287,290,371,419,440,784,811,831,836,837,843,846,849,852,856,888,1139,1181]
  | 478 => [3,21,260,270,279,282,286,287,371,419,440,784,811,831,836,837,843,846,848,852,856,886,1139,1159,1181]
  | 480 => [3,21,260,270,279,282,286,290,371,419,437,440,784,831,836,837,843,846,856,886,1139,1165]
  | 482 => [3,21,260,270,279,282,286,290,371,419,440,784,831,836,837,843,846,849,856,888,1139,1165]
  | 484 => [3,21,260,270,279,282,286,371,419,440,784,831,836,837,843,846,848,856,886,1139,1159,1165]
  | 486 => [3,21,260,270,282,284,286,287,371,419,429,440,784,811,828,831,837,843,846,852,856,886,1181]
  | 487 => [3,21,260,270,282,284,286,287,371,419,440,784,811,819,828,831,837,843,846,852,856,898,1181]
  | 488 => [3,21,260,270,282,284,286,371,419,429,440,784,828,831,837,843,846,856,886,1165]
  | 489 => [3,21,260,270,282,284,286,371,419,440,784,819,828,831,837,843,846,856,898,1165]
  | 490 => [3,21,260,270,282,286,287,371,419,440,784,811,828,831,836,837,843,846,852,856,886,1139,1181]
  | 492 => [3,21,260,270,282,286,371,419,440,784,828,831,836,837,843,846,856,886,1139,1165]
  | _ => []
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def src756 : List (List Nat) := [[371,843,260,440,3,856,21,1153,420,780,817,5,256,801,265,815],[371,843,260,440,3,856,21,275,876,420,780,817,5,256,801,265,815]]
theorem sourceIDs756 : lowerHistorySourcePremises path756 = src756.map (List.map lowerHistoryBound) := by
  have hb : src756.map (List.map lowerHistoryBound) = expected756 := by
    simp only [src756, expected756, List.map_cons, List.map_nil, bound3, bound5, bound21, bound256, bound260, bound265, bound275, bound371, bound420, bound440, bound780, bound801, bound815, bound817, bound843, bound856, bound876, bound1153]
  exact source756.trans hb.symm
theorem length756 : path756.alternatives = (lowerHistorySourcePremises path756).length := by
  rw [sourceIDs756]
  rfl
theorem binding756 : lowerHistoryPathBinding path756 := by
  apply BindingIds19.pathBinding_from_ids path756 src756 [] recs756 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs756 rfl records756 rfl
  · intro r hr _
    simp only [recs756, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise158)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise156)
  · intro r hr _
    simp only [recs756, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path756] using witness775_projection
    · simpa only [blockWids, path756] using witness775_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path756 recs756 records756 length756 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
open BindingNumeric20
theorem op62 : lowerHistoryNecessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [bv784] := by
  decide +kernel
theorem op63 : lowerHistoryNormalization ([2,1,1],[3,1]) false false = bv810 := by
  norm_num [bv810, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op64 : lowerHistoryNecessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [bv6] := by
  decide +kernel
theorem op65 : lowerHistoryNormalization ([2,1,1,1],[3,1]) false false = bv769 := by
  norm_num [bv769, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op66 : lowerHistoryNecessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [bv13] := by
  decide +kernel
theorem op67 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([2,1,1,1],[3,1]) false = bv1078 := by
  norm_num [bv1078, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op68 : lowerHistoryNormalization ([2,1,1,1,3],[3,1]) true true = bv403 := by
  norm_num [bv403, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op69 : lowerHistoryNecessary ⟨⟨([2,2,1,1,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,1,1,3],[3,1]) = some [bv609] := by
  decide +kernel
theorem op70 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,3],[3,1]) true = bv193 := by
  norm_num [bv193, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op71 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,3],[3,1]) true = bv661 := by
  norm_num [bv661, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op72 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1,3],[3,1]) true = bv206 := by
  norm_num [bv206, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op73 : lowerHistoryPull (lowerHistoryH7) ([2,1,1,1],[3,1]) false = bv220 := by
  norm_num [bv220, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def path757 : LowerHistoryPath := ⟨.mixed,73,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([2,2,1,1,1,3],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
noncomputable def raw757 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv403,bv609,bv193,bv661,bv206],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv403,bv609,bv193,bv661,bv206]]
noncomputable def expected757 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv403,bv609,bv193,bv661,bv206],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv403,bv609,bv193,bv661,bv206]]
theorem structural757 (ops : RootOps19.SourceOps) (b3 b6 b13 b21 b193 b206 b260 b282 b287 b371 b403 b419 b440 b609 b661 b769 b784 b810 b811 b837 b843 b852 b856 b1078 b1165 b1181 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h54 : ops.normalization ([2,1],[3]) true false = b282)
    (h55 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h56 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (h57 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = b287)
    (h58 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = b852)
    (h59 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = b811)
    (h60 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (h61 : ops.normalization ([2,1,1],[3]) true true = b419)
    (h62 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (h63 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (h64 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (h65 : ops.normalization ([2,1,1,1],[3,1]) false false = b769)
    (h66 : ops.necessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [b13])
    (h67 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2,1,1,1],[3,1]) false = b1078)
    (h68 : ops.normalization ([2,1,1,1,3],[3,1]) true true = b403)
    (h69 : ops.necessary ⟨⟨([2,2,1,1,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,1,1,3],[3,1]) = some [b609])
    (h70 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,3],[3,1]) true = b193)
    (h71 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,3],[3,1]) true = b661)
    (h72 : ops.pull (lowerHistoryHN) ([2,1,1,1,3],[3,1]) true = b206)
    : RootOps19.eval ops path757 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b193,b661,b206],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b193,b661,b206]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path757, h0, h1, h2, h3, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h68, h69, h70, h71, h72, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource757 : lowerHistorySourcePremises path757 = raw757.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural757 RootOps19.actualOps bv3 bv6 bv13 bv21 bv193 bv206 bv260 bv282 bv287 bv371 bv403 bv419 bv440 bv609 bv661 bv769 bv784 bv810 bv811 bv837 bv843 bv852 bv856 bv1078 bv1165 bv1181 op0 op1 op2 op3 op54 op55 op56 op57 op58 op59 op60 op61 op62 op63 op64 op65 op66 op67 op68 op69 op70 op71 op72
theorem dedup757 : raw757.map List.eraseDups = expected757 := by
  decide +kernel
theorem source757 : lowerHistorySourcePremises path757 = expected757 := (rawSource757).trans (dedup757)
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def src757 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,1078,403,609,193,661,206],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,1078,403,609,193,661,206]]
theorem sourceIDs757 : lowerHistorySourcePremises path757 = src757.map (List.map lowerHistoryBound) := by
  have hb : src757.map (List.map lowerHistoryBound) = expected757 := by
    simp only [src757, expected757, List.map_cons, List.map_nil, bound3, bound6, bound13, bound21, bound193, bound206, bound260, bound282, bound287, bound371, bound403, bound419, bound440, bound609, bound661, bound769, bound784, bound810, bound811, bound837, bound843, bound852, bound856, bound1078, bound1165, bound1181]
  exact source757.trans hb.symm
theorem length757 : path757.alternatives = (lowerHistorySourcePremises path757).length := by
  rw [sourceIDs757]
  rfl
theorem binding757 : lowerHistoryPathBinding path757 := by
  apply BindingIds19.pathBinding_from_ids path757 src757 [] recs757 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs757 rfl records757 rfl
  · intro r hr _
    simp only [recs757, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise188)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise187)
  · intro r hr _
    simp only [recs757, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path757] using witness625_projection
    · simpa only [blockWids, path757] using witness79_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path757 recs757 records757 length757 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
open BindingNumeric20
theorem op74 : lowerHistoryPull (lowerHistoryH9) ([2,1,1,1],[3,1]) false = bv869 := by
  norm_num [bv869, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op75 : lowerHistoryNormalization ([2,1,1,1,2],[3,1]) true true = bv396 := by
  norm_num [bv396, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op76 : lowerHistoryNecessary ⟨⟨([2,2,1,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,1,1,2],[3,1]) = some [bv653] := by
  decide +kernel
theorem op77 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,2],[3,1]) true = bv215 := by
  norm_num [bv215, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op78 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,2],[3,1]) true = bv706 := by
  norm_num [bv706, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op79 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1,2],[3,1]) true = bv185 := by
  norm_num [bv185, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op80 : lowerHistoryNormalization ([2,1,1,1,1],[3,1]) true false = bv219 := by
  norm_num [bv219, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op81 : lowerHistoryNecessary ⟨⟨([2,2,1,1,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1,1],[3,1]) = some [bv728] := by
  decide +kernel
theorem op82 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,1],[3,1]) true = bv237 := by
  norm_num [bv237, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op83 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,1],[3,1]) true = bv761 := by
  norm_num [bv761, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op84 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1,1],[3,1]) true = bv219 := by
  norm_num [bv219, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op85 : lowerHistoryNormalization ([2,1,1],[3,1]) true false = bv270 := by
  norm_num [bv270, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def path758 : LowerHistoryPath := ⟨.mixed,74,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([2,2,1,1,1,2],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩
noncomputable def raw758 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv869,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv869,bv396,bv653,bv215,bv706,bv185]]
noncomputable def expected758 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv869,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv869,bv396,bv653,bv215,bv706,bv185]]
theorem structural758 (ops : RootOps19.SourceOps) (b3 b6 b13 b21 b185 b215 b220 b260 b282 b287 b371 b396 b419 b440 b653 b706 b769 b784 b810 b811 b837 b843 b852 b856 b869 b1078 b1165 b1181 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h54 : ops.normalization ([2,1],[3]) true false = b282)
    (h55 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h56 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (h57 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = b287)
    (h58 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = b852)
    (h59 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = b811)
    (h60 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (h61 : ops.normalization ([2,1,1],[3]) true true = b419)
    (h62 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (h63 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (h64 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (h65 : ops.normalization ([2,1,1,1],[3,1]) false false = b769)
    (h66 : ops.necessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [b13])
    (h67 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2,1,1,1],[3,1]) false = b1078)
    (h73 : ops.pull (lowerHistoryH7) ([2,1,1,1],[3,1]) false = b220)
    (h74 : ops.pull (lowerHistoryH9) ([2,1,1,1],[3,1]) false = b869)
    (h75 : ops.normalization ([2,1,1,1,2],[3,1]) true true = b396)
    (h76 : ops.necessary ⟨⟨([2,2,1,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,1,1,2],[3,1]) = some [b653])
    (h77 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,2],[3,1]) true = b215)
    (h78 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,2],[3,1]) true = b706)
    (h79 : ops.pull (lowerHistoryHN) ([2,1,1,1,2],[3,1]) true = b185)
    : RootOps19.eval ops path758 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b185],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b185],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b185],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b185]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path758, h0, h1, h2, h3, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h67, h73, h74, h75, h76, h77, h78, h79, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource758 : lowerHistorySourcePremises path758 = raw758.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural758 RootOps19.actualOps bv3 bv6 bv13 bv21 bv185 bv215 bv220 bv260 bv282 bv287 bv371 bv396 bv419 bv440 bv653 bv706 bv769 bv784 bv810 bv811 bv837 bv843 bv852 bv856 bv869 bv1078 bv1165 bv1181 op0 op1 op2 op3 op54 op55 op56 op57 op58 op59 op60 op61 op62 op63 op64 op65 op66 op67 op73 op74 op75 op76 op77 op78 op79
theorem dedup758 : raw758.map List.eraseDups = expected758 := by
  decide +kernel
theorem source758 : lowerHistorySourcePremises path758 = expected758 := (rawSource758).trans (dedup758)
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def src758 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,1078,396,653,215,706,185],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,220,869,396,653,215,706,185],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,1078,396,653,215,706,185],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,220,869,396,653,215,706,185]]
theorem sourceIDs758 : lowerHistorySourcePremises path758 = src758.map (List.map lowerHistoryBound) := by
  have hb : src758.map (List.map lowerHistoryBound) = expected758 := by
    simp only [src758, expected758, List.map_cons, List.map_nil, bound3, bound6, bound13, bound21, bound185, bound215, bound220, bound260, bound282, bound287, bound371, bound396, bound419, bound440, bound653, bound706, bound769, bound784, bound810, bound811, bound837, bound843, bound852, bound856, bound869, bound1078, bound1165, bound1181]
  exact source758.trans hb.symm
theorem length758 : path758.alternatives = (lowerHistorySourcePremises path758).length := by
  rw [sourceIDs758]
  rfl
theorem binding758 : lowerHistoryPathBinding path758 := by
  apply BindingIds19.pathBinding_from_ids path758 src758 [] recs758 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs758 rfl records758 rfl
  · intro r hr _
    simp only [recs758, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise186)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise184)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise185)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise183)
  · intro r hr _
    simp only [recs758, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path758] using witness655_projection
    · simpa only [blockWids, path758] using witness655_projection
    · simpa only [blockWids, path758] using witness85_projection
    · simpa only [blockWids, path758] using witness85_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path758 recs758 records758 length758 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def path759 : LowerHistoryPath := ⟨.mixed,75,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([2,2,1,1,1,1],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
noncomputable def raw759 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv219,bv728,bv237,bv761,bv219],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv219,bv728,bv237,bv761,bv219]]
noncomputable def expected759 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv219,bv728,bv237,bv761],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv219,bv728,bv237,bv761]]
theorem structural759 (ops : RootOps19.SourceOps) (b3 b6 b13 b21 b219 b237 b260 b282 b287 b371 b419 b440 b728 b761 b769 b784 b810 b811 b837 b843 b852 b856 b1165 b1181 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h54 : ops.normalization ([2,1],[3]) true false = b282)
    (h55 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h56 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (h57 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = b287)
    (h58 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = b852)
    (h59 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = b811)
    (h60 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (h61 : ops.normalization ([2,1,1],[3]) true true = b419)
    (h62 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (h63 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (h64 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (h65 : ops.normalization ([2,1,1,1],[3,1]) false false = b769)
    (h66 : ops.necessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [b13])
    (h80 : ops.normalization ([2,1,1,1,1],[3,1]) true false = b219)
    (h81 : ops.necessary ⟨⟨([2,2,1,1,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1,1],[3,1]) = some [b728])
    (h82 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,1],[3,1]) true = b237)
    (h83 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,1],[3,1]) true = b761)
    (h84 : ops.pull (lowerHistoryHN) ([2,1,1,1,1],[3,1]) true = b219)
    : RootOps19.eval ops path759 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b219],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b219]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path759, h0, h1, h2, h3, h54, h55, h56, h57, h58, h59, h60, h61, h62, h63, h64, h65, h66, h80, h81, h82, h83, h84, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource759 : lowerHistorySourcePremises path759 = raw759.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural759 RootOps19.actualOps bv3 bv6 bv13 bv21 bv219 bv237 bv260 bv282 bv287 bv371 bv419 bv440 bv728 bv761 bv769 bv784 bv810 bv811 bv837 bv843 bv852 bv856 bv1165 bv1181 op0 op1 op2 op3 op54 op55 op56 op57 op58 op59 op60 op61 op62 op63 op64 op65 op66 op80 op81 op82 op83 op84
theorem dedup759 : raw759.map List.eraseDups = expected759 := by
  decide +kernel
theorem source759 : lowerHistorySourcePremises path759 = expected759 := (rawSource759).trans (dedup759)
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def src759 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,219,728,237,761],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,219,728,237,761]]
theorem sourceIDs759 : lowerHistorySourcePremises path759 = src759.map (List.map lowerHistoryBound) := by
  have hb : src759.map (List.map lowerHistoryBound) = expected759 := by
    simp only [src759, expected759, List.map_cons, List.map_nil, bound3, bound6, bound13, bound21, bound219, bound237, bound260, bound282, bound287, bound371, bound419, bound440, bound728, bound761, bound769, bound784, bound810, bound811, bound837, bound843, bound852, bound856, bound1165, bound1181]
  exact source759.trans hb.symm
theorem length759 : path759.alternatives = (lowerHistorySourcePremises path759).length := by
  rw [sourceIDs759]
  rfl
theorem binding759 : lowerHistoryPathBinding path759 := by
  apply BindingIds19.pathBinding_from_ids path759 src759 [] recs759 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs759 rfl records759 rfl
  · intro r hr _
    simp only [recs759, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise192)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise191)
  · intro r hr _
    simp only [recs759, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path759] using witness697_projection
    · simpa only [blockWids, path759] using witness91_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path759 recs759 records759 length759 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
open BindingNumeric20
theorem op86 : lowerHistoryNecessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [bv831] := by
  decide +kernel
theorem op87 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) true = bv286 := by
  norm_num [bv286, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op88 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) true = bv846 := by
  norm_num [bv846, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op89 : lowerHistoryPull (lowerHistoryHN) ([2,1,1],[3,1]) true = bv270 := by
  norm_num [bv270, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def path760 : LowerHistoryPath := ⟨.mixed,76,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false)],([2,2,1,1],[3,1,3,1]),(true,false),true,3,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
noncomputable def raw760 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv270,bv831,bv286,bv846,bv270],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv270,bv831,bv286,bv846,bv270]]
noncomputable def expected760 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv270,bv831,bv286,bv846],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv270,bv831,bv286,bv846]]
theorem structural760 (ops : RootOps19.SourceOps) (b3 b21 b260 b270 b282 b286 b287 b371 b419 b440 b784 b811 b831 b837 b843 b846 b852 b856 b1165 b1181 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h54 : ops.normalization ([2,1],[3]) true false = b282)
    (h55 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h56 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (h57 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = b287)
    (h58 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = b852)
    (h59 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = b811)
    (h60 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (h61 : ops.normalization ([2,1,1],[3]) true true = b419)
    (h62 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (h85 : ops.normalization ([2,1,1],[3,1]) true false = b270)
    (h86 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [b831])
    (h87 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) true = b286)
    (h88 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) true = b846)
    (h89 : ops.pull (lowerHistoryHN) ([2,1,1],[3,1]) true = b270)
    : RootOps19.eval ops path760 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b286,b846,b270],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b286,b846,b270]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path760, h0, h1, h2, h3, h54, h55, h56, h57, h58, h59, h60, h61, h62, h85, h86, h87, h88, h89, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource760 : lowerHistorySourcePremises path760 = raw760.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural760 RootOps19.actualOps bv3 bv21 bv260 bv270 bv282 bv286 bv287 bv371 bv419 bv440 bv784 bv811 bv831 bv837 bv843 bv846 bv852 bv856 bv1165 bv1181 op0 op1 op2 op3 op54 op55 op56 op57 op58 op59 op60 op61 op62 op85 op86 op87 op88 op89
theorem dedup760 : raw760.map List.eraseDups = expected760 := by
  decide +kernel
theorem source760 : lowerHistorySourcePremises path760 = expected760 := (rawSource760).trans (dedup760)
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def extraIDs760 : List (List Nat) := [[836,1139,828,886],[836,1139,279,848,1159,886],[836,1139,279,848,278,882],[836,1139,279,290,437,886],[836,1139,279,290,849,888],[836,259,828,1172],[836,259,279,848,1159,1172],[836,259,279,848,278,1171],[836,259,279,290,437,1172],[836,259,279,290,849,1170],[284,429,828,886],[284,429,279,848,1159,886],[284,429,279,848,278,882],[284,429,279,290,437,886],[284,429,279,290,849,888],[284,819,828,898],[284,819,279,848,1159,898],[284,819,279,848,278,897],[284,819,279,290,437,898],[284,819,279,290,849,899]]
noncomputable def extraExpected760 : List (List CertBound) := [[bv836,bv1139,bv828,bv886],[bv836,bv1139,bv279,bv848,bv1159,bv886],[bv836,bv1139,bv279,bv848,bv278,bv882],[bv836,bv1139,bv279,bv290,bv437,bv886],[bv836,bv1139,bv279,bv290,bv849,bv888],[bv836,bv259,bv828,bv1172],[bv836,bv259,bv279,bv848,bv1159,bv1172],[bv836,bv259,bv279,bv848,bv278,bv1171],[bv836,bv259,bv279,bv290,bv437,bv1172],[bv836,bv259,bv279,bv290,bv849,bv1170],[bv284,bv429,bv828,bv886],[bv284,bv429,bv279,bv848,bv1159,bv886],[bv284,bv429,bv279,bv848,bv278,bv882],[bv284,bv429,bv279,bv290,bv437,bv886],[bv284,bv429,bv279,bv290,bv849,bv888],[bv284,bv819,bv828,bv898],[bv284,bv819,bv279,bv848,bv1159,bv898],[bv284,bv819,bv279,bv848,bv278,bv897],[bv284,bv819,bv279,bv290,bv437,bv898],[bv284,bv819,bv279,bv290,bv849,bv899]]
theorem extraValues760 : (List.range 20).map (BindingIds19.extras path760) = extraExpected760 := by
  decide +kernel
theorem extraIDs_sound760 : (List.range extraIDs760.length).map (BindingIds19.extras path760) = extraIDs760.map (List.map lowerHistoryBound) := by
  have hb : extraIDs760.map (List.map lowerHistoryBound) = extraExpected760 := by
    simp only [extraIDs760, extraExpected760, List.map_cons, List.map_nil, bound259, bound278, bound279, bound284, bound290, bound429, bound437, bound819, bound828, bound836, bound848, bound849, bound882, bound886, bound888, bound897, bound898, bound899, bound1139, bound1159, bound1170, bound1171, bound1172]
  exact extraValues760.trans hb.symm
end M7ContinueSep17.Noninitial20260918.B755_760

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B755_760
noncomputable def src760 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,270,831,286,846],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,270,831,286,846]]
theorem sourceIDs760 : lowerHistorySourcePremises path760 = src760.map (List.map lowerHistoryBound) := by
  have hb : src760.map (List.map lowerHistoryBound) = expected760 := by
    simp only [src760, expected760, List.map_cons, List.map_nil, bound3, bound21, bound260, bound270, bound282, bound286, bound287, bound371, bound419, bound440, bound784, bound811, bound831, bound837, bound843, bound846, bound852, bound856, bound1165, bound1181]
  exact source760.trans hb.symm
theorem length760 : path760.alternatives = (lowerHistorySourcePremises path760).length := by
  rw [sourceIDs760]
  rfl
theorem binding760 : lowerHistoryPathBinding path760 := by
  apply BindingIds19.pathBinding_from_ids path760 src760 extraIDs760 recs760 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs760 extraIDs_sound760 records760 rfl
  · intro r hr _
    simp only [recs760, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise492)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise484)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise460)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise480)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise482)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise449)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise447)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise441)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise445)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise446)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise488)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise472)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise456)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise468)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise469)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise489)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise473)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise457)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise470)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise471)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise490)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise478)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise458)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise474)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise476)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise448)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise444)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise440)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise442)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise443)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise486)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise466)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise454)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise462)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise463)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise487)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise467)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise455)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise464)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise465)
  · intro r hr _
    simp only [recs760, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path760] using witness71_projection
    · simpa only [blockWids, path760] using witness71_projection
    · simpa only [blockWids, path760] using witness27_projection
    · simpa only [blockWids, path760] using witness557_projection
    · simpa only [blockWids, path760] using witness174_projection
    · simpa only [blockWids, path760] using witness75_projection
    · simpa only [blockWids, path760] using witness75_projection
    · simpa only [blockWids, path760] using witness31_projection
    · simpa only [blockWids, path760] using witness561_projection
    · simpa only [blockWids, path760] using witness178_projection
    · simpa only [blockWids, path760] using witness313_projection
    · simpa only [blockWids, path760] using witness313_projection
    · simpa only [blockWids, path760] using witness17_projection
    · simpa only [blockWids, path760] using witness547_projection
    · simpa only [blockWids, path760] using witness164_projection
    · simpa only [blockWids, path760] using witness59_projection
    · simpa only [blockWids, path760] using witness59_projection
    · simpa only [blockWids, path760] using witness21_projection
    · simpa only [blockWids, path760] using witness551_projection
    · simpa only [blockWids, path760] using witness168_projection
    · simpa only [blockWids, path760] using witness154_projection
    · simpa only [blockWids, path760] using witness154_projection
    · simpa only [blockWids, path760] using witness27_projection
    · simpa only [blockWids, path760] using witness557_projection
    · simpa only [blockWids, path760] using witness174_projection
    · simpa only [blockWids, path760] using witness158_projection
    · simpa only [blockWids, path760] using witness158_projection
    · simpa only [blockWids, path760] using witness31_projection
    · simpa only [blockWids, path760] using witness561_projection
    · simpa only [blockWids, path760] using witness178_projection
    · simpa only [blockWids, path760] using witness109_projection
    · simpa only [blockWids, path760] using witness109_projection
    · simpa only [blockWids, path760] using witness17_projection
    · simpa only [blockWids, path760] using witness547_projection
    · simpa only [blockWids, path760] using witness164_projection
    · simpa only [blockWids, path760] using witness112_projection
    · simpa only [blockWids, path760] using witness112_projection
    · simpa only [blockWids, path760] using witness21_projection
    · simpa only [blockWids, path760] using witness551_projection
    · simpa only [blockWids, path760] using witness168_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path760 recs760 records760 length760 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B755_760

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
namespace M7ContinueSep17.Noninitial20260918.B755_760
theorem _root_.solution : lowerHistoryBindingBatch 755 760 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[755]? = some M7ContinueSep17.Noninitial20260918.B755_760.path756 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 71 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding756
  · have hl : lowerHistoryPaths[756]? = some M7ContinueSep17.Noninitial20260918.B755_760.path757 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 72 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding757
  · have hl : lowerHistoryPaths[757]? = some M7ContinueSep17.Noninitial20260918.B755_760.path758 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 73 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding758
  · have hl : lowerHistoryPaths[758]? = some M7ContinueSep17.Noninitial20260918.B755_760.path759 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 74 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding759
  · have hl : lowerHistoryPaths[759]? = some M7ContinueSep17.Noninitial20260918.B755_760.path760 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 75 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding760
end M7ContinueSep17.Noninitial20260918.B755_760

#print axioms solution
