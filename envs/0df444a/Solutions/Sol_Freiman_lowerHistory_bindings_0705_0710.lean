-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0705_0710
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T02:00:52.500839+00:00
-- url     : https://prove2.me/submissions/f5908953-f41e-412c-b1cb-a6d495869005

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
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def bv2 : CertBound := ⟨true,false,⟨⟨(-605239/322621),(452861/322621),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩⟩⟩
noncomputable def bv6 : CertBound := ⟨true,false,⟨⟨(-2396241/3388429),(1794784/3388429),(0),(0)⟩,⟨(247/649),(1/649),(0),(0)⟩,⟨(177/454),(-1/454),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv13 : CertBound := ⟨true,false,⟨⟨(-271911/1001627),(203584/1001627),(0),(0)⟩,⟨(446/1177),(1/1177),(0),(0)⟩,⟨(651/1702),(-1/1702),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩⟩⟩
noncomputable def bv21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(10/23),(-1/69),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(271/1006),(-1/1006),(0),(0)⟩⟩⟩
noncomputable def bv185 : CertBound := ⟨true,false,⟨⟨(163/5134),(0),(0),(93/25670)⟩,⟨(63/170),(0),(0),(1/510)⟩,⟨(579/1510),(0),(0),(-1/1510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv215 : CertBound := ⟨true,false,⟨⟨(1346119055150/22945528938527),(8480504750/22945528938527),(0),(0)⟩,⟨(19756/52033),(-1/52033),(0),(0)⟩,⟨(53579/141046),(1/141046),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv219 : CertBound := ⟨true,false,⟨⟨(5937/87770),(0),(0),(707/87770)⟩,⟨(251/670),(0),(0),(1/670)⟩,⟨(105/262),(0),(0),(-1/262)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv220 : CertBound := ⟨true,false,⟨⟨(46348286/642787275),(4919669/257114910),(0),(0)⟩,⟨(231/611),(1/1833),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv237 : CertBound := ⟨true,false,⟨⟨(216319037850/1777699342549),(3376499150/5333098027647),(0),(0)⟩,⟨(3247/8507),(-1/25521),(0),(0)⟩,⟨(25537/66838),(1/66838),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv252 : CertBound := ⟨true,false,⟨⟨(41/185),(0),(0),(32/1295)⟩,⟨(3/10),(0),(0),(1/70)⟩,⟨(29/74),(0),(0),(-1/222)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv255 : CertBound := ⟨true,false,⟨⟨(329014964650/1370729503247),(2276619750/1370729503247),(0),(0)⟩,⟨(4519/12598),(-1/12598),(0),(0)⟩,⟨(12510/34801),(1/34801),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv259 : CertBound := ⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv260 : CertBound := ⟨true,false,⟨⟨(31/100),(0),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv263 : CertBound := ⟨true,false,⟨⟨(13/34),(0),(0),(-7/170)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(63/170),(0),(0),(-1/510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv266 : CertBound := ⟨true,false,⟨⟨(807277100/1984682089),(189129600/73433237293),(0),(0)⟩,⟨(2747/7501),(-1/7501),(0),(0)⟩,⟨(7480/20353),(1/20353),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv270 : CertBound := ⟨true,false,⟨⟨(43/94),(0),(0),(37/658)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv274 : CertBound := ⟨true,false,⟨⟨(8164501/16382860),(11119731/81914300),(0),(0)⟩,⟨(93/262),(1/262),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv278 : CertBound := ⟨true,false,⟨⟨(724335/1125901),0,0,(835040/7881307)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv279 : CertBound := ⟨true,false,⟨⟨(5489/8282),0,0,(513/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
noncomputable def bv282 : CertBound := ⟨true,false,⟨⟨(7/10),(0),(0),(1/70)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv284 : CertBound := ⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv286 : CertBound := ⟨true,false,⟨⟨(8603517050/10310778049),(45310050/10310778049),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(3734/9757),(1/9757),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv287 : CertBound := ⟨true,false,⟨⟨(14844131850/16611163283),(-22622450/16611163283),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(553/1429),(1/1429),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv290 : CertBound := ⟨true,false,⟨⟨(5145/4141),0,0,(3196/28987)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv396 : CertBound := ⟨true,true,⟨⟨(163/5134),(0),(0),(93/25670)⟩,⟨(63/170),(0),(0),(1/510)⟩,⟨(579/1510),(0),(0),(-1/1510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv418 : CertBound := ⟨true,true,⟨⟨(41/185),(0),(0),(32/1295)⟩,⟨(3/10),(0),(0),(1/70)⟩,⟨(29/74),(0),(0),(-1/222)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv419 : CertBound := ⟨true,true,⟨⟨(11/47),(0),(0),(4/329)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv426 : CertBound := ⟨true,true,⟨⟨(13/34),(0),(0),(-7/170)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(63/170),(0),(0),(-1/510)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv429 : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv437 : CertBound := ⟨true,true,⟨⟨(1014069/804215),0,0,(167008/804215)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),(0),(0)⟩,⟨(-1/2),(1/2),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩⟩⟩
noncomputable def bv653 : CertBound := ⟨false,false,⟨⟨(94960/2585869),(259781/2585869),(0),(0)⟩,⟨(446/1177),(1/1177),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv706 : CertBound := ⟨false,false,⟨⟨(1878080276500/25150524470163),(39596495000/25150524470163),(0),(0)⟩,⟨(53579/141046),(1/141046),(0),(0)⟩,⟨(2716/7141),(-1/7141),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv728 : CertBound := ⟨false,false,⟨⟨(731824/7179887),(1465575/7179887),(0),(0)⟩,⟨(247/649),(1/649),(0),(0)⟩,⟨(651/1702),(-1/1702),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv752 : CertBound := ⟨false,false,⟨⟨(1586290/10727197),(3840344/10727197),(0),(0)⟩,⟨(93/262),(1/262),(0),(0)⟩,⟨(4519/12598),(-1/12598),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv761 : CertBound := ⟨false,false,⟨⟨(94485848500/573572201883),(6917647000/5162149816947),(0),(0)⟩,⟨(25537/66838),(1/66838),(0),(0)⟩,⟨(395/1031),(-1/3093),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv769 : CertBound := ⟨false,false,⟨⟨(1101/6157),(0),(0),(128/6157)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(105/262),(0),(0),(-1/262)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv779 : CertBound := ⟨false,false,⟨⟨(7617/30251),(63275/90753),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(66/179),(-1/537),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv784 : CertBound := ⟨false,false,⟨⟨(13766/50713),(29019/50713),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv792 : CertBound := ⟨false,false,⟨⟨(36503093000/123397768611),(1007502500/123397768611),(0),(0)⟩,⟨(12510/34801),(1/34801),(0),(0)⟩,⟨(667/1846),(-1/1846),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv810 : CertBound := ⟨false,false,⟨⟨(43/94),(0),(0),(37/658)⟩,⟨(31/94),(0),(0),(1/94)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv811 : CertBound := ⟨false,false,⟨⟨(437151/916486),(1064107/2749458),(0),(0)⟩,⟨(1991/5521),(1/5521),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(5/22),(1/22),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv813 : CertBound := ⟨false,false,⟨⟨(542698100500/1049991995709),(375206500/33870709539),(0),(0)⟩,⟨(7480/20353),(1/20353),(0),(0)⟩,⟨(383/1033),(-1/1033),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv819 : CertBound := ⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv828 : CertBound := ⟨false,false,⟨⟨(5489/8282),0,0,(513/57974)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
noncomputable def bv831 : CertBound := ⟨false,false,⟨⟨(34974/50713),(213073/152139),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv836 : CertBound := ⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv837 : CertBound := ⟨false,false,⟨⟨(16971/22607),(33730/22607),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv846 : CertBound := ⟨false,false,⟨⟨(124480872500/110611274499),(1112783000/110611274499),(0),(0)⟩,⟨(3734/9757),(1/9757),(0),(0)⟩,⟨(177/454),(-1/454),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(1251/4667),(-1/14001),(0),(0)⟩⟩⟩
noncomputable def bv848 : CertBound := ⟨false,false,⟨⟨(5145/4141),0,0,(3196/28987)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(83/202),0,0,(-1/202)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(115/422),0,0,(-1/1266)⟩⟩⟩
noncomputable def bv849 : CertBound := ⟨false,false,⟨⟨(1014069/804215),0,0,(167008/804215)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv851 : CertBound := ⟨false,false,⟨⟨(13/10),(0),(0),(9/70)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(1/2),(0),(0),(-1/42)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(31/94),(0),(0),(-1/94)⟩⟩⟩
noncomputable def bv852 : CertBound := ⟨false,false,⟨⟨(123317000/92840319),(-6536000/278520957),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(1809/6094),(1/6094),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv856 : CertBound := ⟨false,false,⟨⟨(3/2),(0),(0),(1/10)⟩,⟨(-1/10),(0),(0),(1/10)⟩,⟨(9/10),(0),(0),(-1/10)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(15/34),(0),(0),(-1/34)⟩⟩⟩
noncomputable def bv869 : CertBound := ⟨false,false,⟨⟨(1208703/351923),(-659041/351923),(0),(0)⟩,⟨(7/23),(1/23),(0),(0)⟩,⟨(446/1177),(1/1177),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv878 : CertBound := ⟨false,false,⟨⟨(6639/169),(-3704/169),(0),(0)⟩,⟨(-1/2),(1/2),(0),(0)⟩,⟨(61/169),(1/169),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv882 : CertBound := ⟨false,true,⟨⟨(-2688/2497),(2219/2497),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv886 : CertBound := ⟨false,true,⟨⟨(-189063/182281),(473333/546843),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv888 : CertBound := ⟨false,true,⟨⟨(-6713195/6707459),(5674580/6707459),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv897 : CertBound := ⟨false,true,⟨⟨(-19457/64922),(30367/64922),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv898 : CertBound := ⟨false,true,⟨⟨(-2013760/7108959),(3254539/7108959),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv899 : CertBound := ⟨false,true,⟨⟨(-64591922/261590901),(114640810/261590901),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
noncomputable def bv1078 : CertBound := ⟨false,true,⟨⟨(46348286/642787275),(4919669/257114910),(0),(0)⟩,⟨(231/611),(1/1833),(0),(0)⟩,⟨(32/83),(-1/249),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv1139 : CertBound := ⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
noncomputable def bv1152 : CertBound := ⟨false,true,⟨⟨(8164501/16382860),(11119731/81914300),(0),(0)⟩,⟨(93/262),(1/262),(0),(0)⟩,⟨(15/37),(-1/37),(0),(0)⟩,⟨(83/313),(1/313),(0),(0)⟩,⟨(133/478),(-1/478),(0),(0)⟩⟩⟩
noncomputable def bv1159 : CertBound := ⟨false,true,⟨⟨(724335/1125901),0,0,(835040/7881307)⟩,⟨(31/82),0,0,(1/574)⟩,⟨(3035/7846),0,0,(-1/7846)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
noncomputable def bv1165 : CertBound := ⟨false,true,⟨⟨(14844131850/16611163283),(-22622450/16611163283),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(553/1429),(1/1429),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
noncomputable def bv1170 : CertBound := ⟨false,true,⟨⟨(2386542/2113309),(-1499437/4226618),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(3230/8353),(-1/8353),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
noncomputable def bv1171 : CertBound := ⟨false,true,⟨⟨(184911237/163006657),(-58481983/163006657),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
noncomputable def bv1172 : CertBound := ⟨false,true,⟨⟨(662039/574310),(-212429/574310),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
noncomputable def bv1181 : CertBound := ⟨false,true,⟨⟨(2754444750/2052479143),(-216932250/2052479143),(0),(0)⟩,⟨(35/94),(1/94),(0),(0)⟩,⟨(1413/3718),(-1/3718),(0),(0)⟩,⟨(16/59),(1/177),(0),(0)⟩,⟨(43/142),(-1/142),(0),(0)⟩⟩⟩
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [bv371,bv843,bv260,bv440] := by
  simpa only [bv371,bv843,bv260,bv440] using BindingNumeric20.initial_base
theorem op1 : lowerHistoryRelaxedGoodness ⟨([1],[3,1]),(false,false)⟩ = some [bv3] := by
  decide +kernel
theorem op2 : lowerHistoryNormalization ([2],[3]) false false = bv856 := by
  norm_num [bv856, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op3 : lowerHistoryNecessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [bv21] := by
  decide +kernel
theorem op37 : lowerHistoryNormalization ([2,1],[3]) true false = bv282 := by
  norm_num [bv282, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op38 : lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [bv837] := by
  decide +kernel
theorem op39 : lowerHistoryPull (lowerHistoryH2) ([2,1],[3]) true = bv1165 := by
  norm_num [bv1165, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op40 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = bv287 := by
  norm_num [bv287, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op41 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = bv852 := by
  norm_num [bv852, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op42 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = bv811 := by
  norm_num [bv811, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op43 : lowerHistoryPull (lowerHistoryH23) ([2,1],[3]) true = bv1181 := by
  norm_num [bv1181, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op44 : lowerHistoryNormalization ([2,1,1],[3]) true true = bv419 := by
  norm_num [bv419, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
open BindingNumeric20
theorem op45 : lowerHistoryNecessary ⟨⟨([1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [bv784] := by
  decide +kernel
theorem op46 : lowerHistoryNormalization ([2,1,1],[3,1]) false false = bv810 := by
  norm_num [bv810, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op47 : lowerHistoryNecessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [bv6] := by
  decide +kernel
theorem op48 : lowerHistoryNormalization ([2,1,1,1],[3,1]) false false = bv769 := by
  norm_num [bv769, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op49 : lowerHistoryNecessary ⟨⟨([1,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [bv13] := by
  decide +kernel
theorem op50 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([2,1,1,1],[3,1]) false = bv1078 := by
  norm_num [bv1078, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op56 : lowerHistoryPull (lowerHistoryH7) ([2,1,1,1],[3,1]) false = bv220 := by
  norm_num [bv220, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op57 : lowerHistoryPull (lowerHistoryH9) ([2,1,1,1],[3,1]) false = bv869 := by
  norm_num [bv869, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op58 : lowerHistoryNormalization ([2,1,1,1,2],[3,1]) true true = bv396 := by
  norm_num [bv396, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op59 : lowerHistoryNecessary ⟨⟨([1,2,1,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,1,1,2],[3,1]) = some [bv653] := by
  decide +kernel
theorem op60 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,2],[3,1]) true = bv215 := by
  norm_num [bv215, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op61 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,2],[3,1]) true = bv706 := by
  norm_num [bv706, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
open BindingNumeric20
theorem op62 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1,2],[3,1]) true = bv185 := by
  norm_num [bv185, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op63 : lowerHistoryNormalization ([2,1,1,1,1],[3,1]) true false = bv219 := by
  norm_num [bv219, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op64 : lowerHistoryNecessary ⟨⟨([1,2,1,1,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1,1],[3,1]) = some [bv728] := by
  decide +kernel
theorem op65 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,1],[3,1]) true = bv237 := by
  norm_num [bv237, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op66 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,1],[3,1]) true = bv761 := by
  norm_num [bv761, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op67 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1,1],[3,1]) true = bv219 := by
  norm_num [bv219, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op68 : lowerHistoryNormalization ([2,1,1],[3,1]) true false = bv270 := by
  norm_num [bv270, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op69 : lowerHistoryNecessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [bv831] := by
  decide +kernel
theorem op70 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) true = bv286 := by
  norm_num [bv286, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op71 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) true = bv846 := by
  norm_num [bv846, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op72 : lowerHistoryPull (lowerHistoryHN) ([2,1,1],[3,1]) true = bv270 := by
  norm_num [bv270, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op73 : lowerHistoryNormalization ([2,1],[3,1]) false false = bv851 := by
  norm_num [bv851, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def path706 : LowerHistoryPath := ⟨.mixed,22,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([1,2,1,1,1,2],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
noncomputable def raw706 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv869,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv869,bv396,bv653,bv215,bv706,bv185]]
noncomputable def expected706 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv869,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv1078,bv396,bv653,bv215,bv706,bv185],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv220,bv869,bv396,bv653,bv215,bv706,bv185]]
theorem structural706 (ops : RootOps19.SourceOps) (b3 b6 b13 b21 b185 b215 b220 b260 b282 b287 b371 b396 b419 b440 b653 b706 b769 b784 b810 b811 b837 b843 b852 b856 b869 b1078 b1165 b1181 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h37 : ops.normalization ([2,1],[3]) true false = b282)
    (h38 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h39 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = b287)
    (h41 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = b852)
    (h42 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = b811)
    (h43 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (h44 : ops.normalization ([2,1,1],[3]) true true = b419)
    (h45 : ops.necessary ⟨⟨([1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (h46 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (h47 : ops.necessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (h48 : ops.normalization ([2,1,1,1],[3,1]) false false = b769)
    (h49 : ops.necessary ⟨⟨([1,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [b13])
    (h50 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2,1,1,1],[3,1]) false = b1078)
    (h56 : ops.pull (lowerHistoryH7) ([2,1,1,1],[3,1]) false = b220)
    (h57 : ops.pull (lowerHistoryH9) ([2,1,1,1],[3,1]) false = b869)
    (h58 : ops.normalization ([2,1,1,1,2],[3,1]) true true = b396)
    (h59 : ops.necessary ⟨⟨([1,2,1,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,1,1,2],[3,1]) = some [b653])
    (h60 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,2],[3,1]) true = b215)
    (h61 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,2],[3,1]) true = b706)
    (h62 : ops.pull (lowerHistoryHN) ([2,1,1,1,2],[3,1]) true = b185)
    : RootOps19.eval ops path706 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b185],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b185],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b185],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b185]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([1,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path706, h0, h1, h2, h3, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h50, h56, h57, h58, h59, h60, h61, h62, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource706 : lowerHistorySourcePremises path706 = raw706.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural706 RootOps19.actualOps bv3 bv6 bv13 bv21 bv185 bv215 bv220 bv260 bv282 bv287 bv371 bv396 bv419 bv440 bv653 bv706 bv769 bv784 bv810 bv811 bv837 bv843 bv852 bv856 bv869 bv1078 bv1165 bv1181 op0 op1 op2 op3 op37 op38 op39 op40 op41 op42 op43 op44 op45 op46 op47 op48 op49 op50 op56 op57 op58 op59 op60 op61 op62
theorem dedup706 : raw706.map List.eraseDups = expected706 := by
  decide +kernel
theorem source706 : lowerHistorySourcePremises path706 = expected706 := (rawSource706).trans (dedup706)
end M7ContinueSep17.Noninitial20260918.B705_710

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
namespace M7ContinueSep17.Noninitial20260918.B705_710
theorem bound2 : lowerHistoryBound 2 = bv2 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[1]? = some bv2 := Eq.refl (some bv2)
  exact (BoundCompact16.global_to_chunk1 1 (by decide)).trans hl
theorem bound3 : lowerHistoryBound 3 = bv3 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[2]? = some bv3 := Eq.refl (some bv3)
  exact (BoundCompact16.global_to_chunk1 2 (by decide)).trans hl
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
theorem bound252 : lowerHistoryBound 252 = bv252 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[51]? = some bv252 := Eq.refl (some bv252)
  exact (BoundCompact16.global_to_chunk2 51 (by decide)).trans hl
theorem bound255 : lowerHistoryBound 255 = bv255 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[54]? = some bv255 := Eq.refl (some bv255)
  exact (BoundCompact16.global_to_chunk2 54 (by decide)).trans hl
theorem bound259 : lowerHistoryBound 259 = bv259 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[58]? = some bv259 := Eq.refl (some bv259)
  exact (BoundCompact16.global_to_chunk2 58 (by decide)).trans hl
theorem bound260 : lowerHistoryBound 260 = bv260 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[59]? = some bv260 := Eq.refl (some bv260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hl
theorem bound263 : lowerHistoryBound 263 = bv263 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[62]? = some bv263 := Eq.refl (some bv263)
  exact (BoundCompact16.global_to_chunk2 62 (by decide)).trans hl
theorem bound266 : lowerHistoryBound 266 = bv266 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[65]? = some bv266 := Eq.refl (some bv266)
  exact (BoundCompact16.global_to_chunk2 65 (by decide)).trans hl
theorem bound270 : lowerHistoryBound 270 = bv270 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[69]? = some bv270 := Eq.refl (some bv270)
  exact (BoundCompact16.global_to_chunk2 69 (by decide)).trans hl
theorem bound274 : lowerHistoryBound 274 = bv274 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[73]? = some bv274 := Eq.refl (some bv274)
  exact (BoundCompact16.global_to_chunk2 73 (by decide)).trans hl
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
theorem bound418 : lowerHistoryBound 418 = bv418 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[17]? = some bv418 := Eq.refl (some bv418)
  exact (BoundCompact16.global_to_chunk3 17 (by decide)).trans hl
theorem bound419 : lowerHistoryBound 419 = bv419 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[18]? = some bv419 := Eq.refl (some bv419)
  exact (BoundCompact16.global_to_chunk3 18 (by decide)).trans hl
theorem bound426 : lowerHistoryBound 426 = bv426 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[25]? = some bv426 := Eq.refl (some bv426)
  exact (BoundCompact16.global_to_chunk3 25 (by decide)).trans hl
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
theorem bound653 : lowerHistoryBound 653 = bv653 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[52]? = some bv653 := Eq.refl (some bv653)
  exact (BoundCompact16.global_to_chunk4 52 (by decide)).trans hl
theorem bound706 : lowerHistoryBound 706 = bv706 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[105]? = some bv706 := Eq.refl (some bv706)
  exact (BoundCompact16.global_to_chunk4 105 (by decide)).trans hl
theorem bound728 : lowerHistoryBound 728 = bv728 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[127]? = some bv728 := Eq.refl (some bv728)
  exact (BoundCompact16.global_to_chunk4 127 (by decide)).trans hl
theorem bound752 : lowerHistoryBound 752 = bv752 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[151]? = some bv752 := Eq.refl (some bv752)
  exact (BoundCompact16.global_to_chunk4 151 (by decide)).trans hl
theorem bound761 : lowerHistoryBound 761 = bv761 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[160]? = some bv761 := Eq.refl (some bv761)
  exact (BoundCompact16.global_to_chunk4 160 (by decide)).trans hl
theorem bound769 : lowerHistoryBound 769 = bv769 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[168]? = some bv769 := Eq.refl (some bv769)
  exact (BoundCompact16.global_to_chunk4 168 (by decide)).trans hl
theorem bound779 : lowerHistoryBound 779 = bv779 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[178]? = some bv779 := Eq.refl (some bv779)
  exact (BoundCompact16.global_to_chunk4 178 (by decide)).trans hl
theorem bound784 : lowerHistoryBound 784 = bv784 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[183]? = some bv784 := Eq.refl (some bv784)
  exact (BoundCompact16.global_to_chunk4 183 (by decide)).trans hl
theorem bound792 : lowerHistoryBound 792 = bv792 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[191]? = some bv792 := Eq.refl (some bv792)
  exact (BoundCompact16.global_to_chunk4 191 (by decide)).trans hl
theorem bound810 : lowerHistoryBound 810 = bv810 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[9]? = some bv810 := Eq.refl (some bv810)
  exact (BoundCompact16.global_to_chunk5 9 (by decide)).trans hl
theorem bound811 : lowerHistoryBound 811 = bv811 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[10]? = some bv811 := Eq.refl (some bv811)
  exact (BoundCompact16.global_to_chunk5 10 (by decide)).trans hl
theorem bound813 : lowerHistoryBound 813 = bv813 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[12]? = some bv813 := Eq.refl (some bv813)
  exact (BoundCompact16.global_to_chunk5 12 (by decide)).trans hl
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
theorem bound851 : lowerHistoryBound 851 = bv851 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[50]? = some bv851 := Eq.refl (some bv851)
  exact (BoundCompact16.global_to_chunk5 50 (by decide)).trans hl
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
theorem bound878 : lowerHistoryBound 878 = bv878 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[77]? = some bv878 := Eq.refl (some bv878)
  exact (BoundCompact16.global_to_chunk5 77 (by decide)).trans hl
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
theorem bound1152 : lowerHistoryBound 1152 = bv1152 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[151]? = some bv1152 := Eq.refl (some bv1152)
  exact (BoundCompact16.global_to_chunk6 151).trans hl
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
end M7ContinueSep17.Noninitial20260918.B705_710

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
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def recs706 : List LowerHistoryRecord := [⟨.mixed,22,0,(-1),false,186,656⟩,⟨.mixed,22,1,(-1),false,184,656⟩,⟨.mixed,22,2,(-1),false,185,86⟩,⟨.mixed,22,3,(-1),false,183,86⟩]
theorem records706 : lowerHistoryRecordsFor (⟨.mixed,22,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([1,2,1,1,1,2],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩ : LowerHistoryPath) = recs706 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 22)) = recs706
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs707 : List LowerHistoryRecord := [⟨.mixed,23,0,(-1),false,192,698⟩,⟨.mixed,23,1,(-1),false,191,92⟩]
theorem records707 : lowerHistoryRecordsFor (⟨.mixed,23,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([1,2,1,1,1,1],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs707 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 23)) = recs707
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs708 : List LowerHistoryRecord := [⟨.mixed,24,0,0,false,492,72⟩,⟨.mixed,24,0,1,false,484,72⟩,⟨.mixed,24,0,2,false,460,28⟩,⟨.mixed,24,0,3,false,480,558⟩,⟨.mixed,24,0,4,false,482,175⟩,⟨.mixed,24,0,5,false,449,76⟩,⟨.mixed,24,0,6,false,447,76⟩,⟨.mixed,24,0,7,false,441,32⟩,⟨.mixed,24,0,8,false,445,562⟩,⟨.mixed,24,0,9,false,446,179⟩,⟨.mixed,24,0,10,false,488,314⟩,⟨.mixed,24,0,11,false,472,314⟩,⟨.mixed,24,0,12,false,456,18⟩,⟨.mixed,24,0,13,false,468,548⟩,⟨.mixed,24,0,14,false,469,165⟩,⟨.mixed,24,0,15,false,489,60⟩,⟨.mixed,24,0,16,false,473,60⟩,⟨.mixed,24,0,17,false,457,22⟩,⟨.mixed,24,0,18,false,470,552⟩,⟨.mixed,24,0,19,false,471,169⟩,⟨.mixed,24,1,0,false,490,155⟩,⟨.mixed,24,1,1,false,478,155⟩,⟨.mixed,24,1,2,false,458,28⟩,⟨.mixed,24,1,3,false,474,558⟩,⟨.mixed,24,1,4,false,476,175⟩,⟨.mixed,24,1,5,false,448,159⟩,⟨.mixed,24,1,6,false,444,159⟩,⟨.mixed,24,1,7,false,440,32⟩,⟨.mixed,24,1,8,false,442,562⟩,⟨.mixed,24,1,9,false,443,179⟩,⟨.mixed,24,1,10,false,486,314⟩,⟨.mixed,24,1,11,false,466,314⟩,⟨.mixed,24,1,12,false,454,18⟩,⟨.mixed,24,1,13,false,462,548⟩,⟨.mixed,24,1,14,false,463,165⟩,⟨.mixed,24,1,15,false,487,113⟩,⟨.mixed,24,1,16,false,467,113⟩,⟨.mixed,24,1,17,false,455,22⟩,⟨.mixed,24,1,18,false,464,552⟩,⟨.mixed,24,1,19,false,465,169⟩]
theorem records708 : lowerHistoryRecordsFor (⟨.mixed,24,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false)],([1,2,1,1],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs708 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 24)) = recs708
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs709 : List LowerHistoryRecord := [⟨.mixed,25,0,(-1),false,45,746⟩]
theorem records709 : lowerHistoryRecordsFor (⟨.mixed,25,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([3],[]),true)],([1,2,1,3],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩ : LowerHistoryPath) = recs709 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 25)) = recs709
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
noncomputable def recs710 : List LowerHistoryRecord := [⟨.mixed,26,0,(-1),false,44,764⟩,⟨.mixed,26,1,(-1),false,43,764⟩]
theorem records710 : lowerHistoryRecordsFor (⟨.mixed,26,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([2],[]),true)],([1,2,1,2],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩ : LowerHistoryPath) = recs710 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .mixed).filter (fun r => decide (r.catalog = .mixed ∧ r.pathId = 26)) = recs710
  rw [M7ContinueSep17.CatalogueGeneral.catalogListM]
  rfl
end M7ContinueSep17.Noninitial20260918.B705_710

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
namespace M7ContinueSep17.Noninitial20260918.B705_710
theorem premise43 : lowerHistoryPremises[42]? = some ([2,3,21,252,260,266,274,282,371,418,440,779,813,837,843,851,856,878] : List Nat) := by
  have hg : lowerHistoryPremises[42]? = lowerHistoryPremises01[42]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 42 (by decide)
  exact hg.trans (by rfl)
theorem premise44 : lowerHistoryPremises[43]? = some ([2,3,21,252,260,266,282,371,418,440,779,813,837,843,851,856,1152] : List Nat) := by
  have hg : lowerHistoryPremises[43]? = lowerHistoryPremises01[43]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 43 (by decide)
  exact hg.trans (by rfl)
theorem premise45 : lowerHistoryPremises[44]? = some ([2,3,21,255,260,263,282,371,426,440,752,792,837,843,851,856,1152] : List Nat) := by
  have hg : lowerHistoryPremises[44]? = lowerHistoryPremises01[44]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 44 (by decide)
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
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Noninitial20260918.B705_710
theorem witness18_projection : (lowerHistoryWitness 18).lowerBound = lowerHistoryBound 278 ∧ (lowerHistoryWitness 18).upperBound = lowerHistoryBound 882 ∧ (lowerHistoryWitness 18).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[17]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 278, lowerHistoryBound 882, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 278, lowerHistoryBound 882, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[17]? = lowerHistoryWitnesses01[17]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 17 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness22_projection : (lowerHistoryWitness 22).lowerBound = lowerHistoryBound 278 ∧ (lowerHistoryWitness 22).upperBound = lowerHistoryBound 897 ∧ (lowerHistoryWitness 22).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[21]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 278, lowerHistoryBound 897, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 278, lowerHistoryBound 897, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[21]? = lowerHistoryWitnesses01[21]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 21 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness28_projection : (lowerHistoryWitness 28).lowerBound = lowerHistoryBound 278 ∧ (lowerHistoryWitness 28).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 28).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[27]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 278, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 278, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[27]? = lowerHistoryWitnesses01[27]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 27 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness32_projection : (lowerHistoryWitness 32).lowerBound = lowerHistoryBound 278 ∧ (lowerHistoryWitness 32).upperBound = lowerHistoryBound 1171 ∧ (lowerHistoryWitness 32).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[31]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 278, lowerHistoryBound 1171, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 278, lowerHistoryBound 1171, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[31]? = lowerHistoryWitnesses01[31]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 31 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness60_projection : (lowerHistoryWitness 60).lowerBound = lowerHistoryBound 286 ∧ (lowerHistoryWitness 60).upperBound = lowerHistoryBound 898 ∧ (lowerHistoryWitness 60).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[59]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 286, lowerHistoryBound 898, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 286, lowerHistoryBound 898, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[59]? = lowerHistoryWitnesses01[59]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 59 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness72_projection : (lowerHistoryWitness 72).lowerBound = lowerHistoryBound 286 ∧ (lowerHistoryWitness 72).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 72).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[71]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 286, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 286, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[71]? = lowerHistoryWitnesses01[71]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 71 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness76_projection : (lowerHistoryWitness 76).lowerBound = lowerHistoryBound 286 ∧ (lowerHistoryWitness 76).upperBound = lowerHistoryBound 1172 ∧ (lowerHistoryWitness 76).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[75]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 286, lowerHistoryBound 1172, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 286, lowerHistoryBound 1172, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[75]? = lowerHistoryWitnesses01[75]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 75 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness86_projection : (lowerHistoryWitness 86).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 86).upperBound = lowerHistoryBound 706 ∧ (lowerHistoryWitness 86).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[85]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 706, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 706, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[85]? = lowerHistoryWitnesses01[85]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 85 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness92_projection : (lowerHistoryWitness 92).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 92).upperBound = lowerHistoryBound 761 ∧ (lowerHistoryWitness 92).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[91]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 761, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 761, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[91]? = lowerHistoryWitnesses01[91]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 91 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness113_projection : (lowerHistoryWitness 113).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 113).upperBound = lowerHistoryBound 898 ∧ (lowerHistoryWitness 113).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[112]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 898, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 898, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[112]? = lowerHistoryWitnesses01[112]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 112 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness155_projection : (lowerHistoryWitness 155).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 155).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 155).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[154]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[154]? = lowerHistoryWitnesses01[154]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 154 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness159_projection : (lowerHistoryWitness 159).lowerBound = lowerHistoryBound 287 ∧ (lowerHistoryWitness 159).upperBound = lowerHistoryBound 1172 ∧ (lowerHistoryWitness 159).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[158]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 1172, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 1172, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[158]? = lowerHistoryWitnesses01[158]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 158 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness165_projection : (lowerHistoryWitness 165).lowerBound = lowerHistoryBound 290 ∧ (lowerHistoryWitness 165).upperBound = lowerHistoryBound 888 ∧ (lowerHistoryWitness 165).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[164]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 290, lowerHistoryBound 888, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 290, lowerHistoryBound 888, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[164]? = lowerHistoryWitnesses01[164]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 164 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness169_projection : (lowerHistoryWitness 169).lowerBound = lowerHistoryBound 290 ∧ (lowerHistoryWitness 169).upperBound = lowerHistoryBound 899 ∧ (lowerHistoryWitness 169).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[168]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 290, lowerHistoryBound 899, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 290, lowerHistoryBound 899, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[168]? = lowerHistoryWitnesses01[168]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 168 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness175_projection : (lowerHistoryWitness 175).lowerBound = lowerHistoryBound 290 ∧ (lowerHistoryWitness 175).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 175).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[174]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 290, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 290, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[174]? = lowerHistoryWitnesses01[174]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 174 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness179_projection : (lowerHistoryWitness 179).lowerBound = lowerHistoryBound 290 ∧ (lowerHistoryWitness 179).upperBound = lowerHistoryBound 1170 ∧ (lowerHistoryWitness 179).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[178]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 290, lowerHistoryBound 1170, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 290, lowerHistoryBound 1170, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[178]? = lowerHistoryWitnesses01[178]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk1 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 178 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness314_projection : (lowerHistoryWitness 314).lowerBound = lowerHistoryBound 429 ∧ (lowerHistoryWitness 314).upperBound = lowerHistoryBound 886 ∧ (lowerHistoryWitness 314).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[113]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 429, lowerHistoryBound 886, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 429, lowerHistoryBound 886, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[313]? = lowerHistoryWitnesses02[113]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 113 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness548_projection : (lowerHistoryWitness 548).lowerBound = lowerHistoryBound 437 ∧ (lowerHistoryWitness 548).upperBound = lowerHistoryBound 886 ∧ (lowerHistoryWitness 548).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[147]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 437, lowerHistoryBound 886, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 437, lowerHistoryBound 886, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[547]? = lowerHistoryWitnesses03[147]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 147 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness552_projection : (lowerHistoryWitness 552).lowerBound = lowerHistoryBound 437 ∧ (lowerHistoryWitness 552).upperBound = lowerHistoryBound 898 ∧ (lowerHistoryWitness 552).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[151]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 437, lowerHistoryBound 898, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 437, lowerHistoryBound 898, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[551]? = lowerHistoryWitnesses03[151]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 151 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness558_projection : (lowerHistoryWitness 558).lowerBound = lowerHistoryBound 437 ∧ (lowerHistoryWitness 558).upperBound = lowerHistoryBound 1139 ∧ (lowerHistoryWitness 558).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[157]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 437, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 437, lowerHistoryBound 1139, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[557]? = lowerHistoryWitnesses03[157]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 157 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness562_projection : (lowerHistoryWitness 562).lowerBound = lowerHistoryBound 437 ∧ (lowerHistoryWitness 562).upperBound = lowerHistoryBound 1172 ∧ (lowerHistoryWitness 562).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[161]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 437, lowerHistoryBound 1172, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 437, lowerHistoryBound 1172, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[561]? = lowerHistoryWitnesses03[161]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 161 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness656_projection : (lowerHistoryWitness 656).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 656).upperBound = lowerHistoryBound 706 ∧ (lowerHistoryWitness 656).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[55]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 706, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 706, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[655]? = lowerHistoryWitnesses04[55]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 55 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness698_projection : (lowerHistoryWitness 698).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 698).upperBound = lowerHistoryBound 761 ∧ (lowerHistoryWitness 698).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[97]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 761, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 761, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[697]? = lowerHistoryWitnesses04[97]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 97 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness746_projection : (lowerHistoryWitness 746).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 746).upperBound = lowerHistoryBound 792 ∧ (lowerHistoryWitness 746).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[145]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 792, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 792, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[745]? = lowerHistoryWitnesses04[145]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 145 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness764_projection : (lowerHistoryWitness 764).lowerBound = lowerHistoryBound 440 ∧ (lowerHistoryWitness 764).upperBound = lowerHistoryBound 813 ∧ (lowerHistoryWitness 764).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses04[163]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 813, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 813, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[763]? = lowerHistoryWitnesses04[163]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 163 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 18 => (278,882)
  | 22 => (278,897)
  | 28 => (278,1139)
  | 32 => (278,1171)
  | 60 => (286,898)
  | 72 => (286,1139)
  | 76 => (286,1172)
  | 86 => (287,706)
  | 92 => (287,761)
  | 113 => (287,898)
  | 155 => (287,1139)
  | 159 => (287,1172)
  | 165 => (290,888)
  | 169 => (290,899)
  | 175 => (290,1139)
  | 179 => (290,1170)
  | 314 => (429,886)
  | 548 => (437,886)
  | 552 => (437,898)
  | 558 => (437,1139)
  | 562 => (437,1172)
  | 656 => (440,706)
  | 698 => (440,761)
  | 746 => (440,792)
  | 764 => (440,813)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 43 => [2,3,21,252,260,266,274,282,371,418,440,779,813,837,843,851,856,878]
  | 44 => [2,3,21,252,260,266,282,371,418,440,779,813,837,843,851,856,1152]
  | 45 => [2,3,21,255,260,263,282,371,426,440,752,792,837,843,851,856,1152]
  | 183 => [3,6,13,21,185,215,220,260,282,287,371,396,419,440,653,706,769,784,810,811,837,843,852,856,869,1181]
  | 184 => [3,6,13,21,185,215,220,260,282,371,396,419,440,653,706,769,784,810,837,843,856,869,1165]
  | 185 => [3,6,13,21,185,215,260,282,287,371,396,419,440,653,706,769,784,810,811,837,843,852,856,1078,1181]
  | 186 => [3,6,13,21,185,215,260,282,371,396,419,440,653,706,769,784,810,837,843,856,1078,1165]
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
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def src706 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,1078,396,653,215,706,185],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,220,869,396,653,215,706,185],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,1078,396,653,215,706,185],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,220,869,396,653,215,706,185]]
theorem sourceIDs706 : lowerHistorySourcePremises path706 = src706.map (List.map lowerHistoryBound) := by
  have hb : src706.map (List.map lowerHistoryBound) = expected706 := by
    simp only [src706, expected706, List.map_cons, List.map_nil, bound3, bound6, bound13, bound21, bound185, bound215, bound220, bound260, bound282, bound287, bound371, bound396, bound419, bound440, bound653, bound706, bound769, bound784, bound810, bound811, bound837, bound843, bound852, bound856, bound869, bound1078, bound1165, bound1181]
  exact source706.trans hb.symm
theorem length706 : path706.alternatives = (lowerHistorySourcePremises path706).length := by
  rw [sourceIDs706]
  rfl
theorem binding706 : lowerHistoryPathBinding path706 := by
  apply BindingIds19.pathBinding_from_ids path706 src706 [] recs706 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs706 rfl records706 rfl
  · intro r hr _
    simp only [recs706, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise186)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise184)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise185)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise183)
  · intro r hr _
    simp only [recs706, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path706] using witness656_projection
    · simpa only [blockWids, path706] using witness656_projection
    · simpa only [blockWids, path706] using witness86_projection
    · simpa only [blockWids, path706] using witness86_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path706 recs706 records706 length706 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def path707 : LowerHistoryPath := ⟨.mixed,23,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([1,2,1,1,1,1],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
noncomputable def raw707 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv219,bv728,bv237,bv761,bv219],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv219,bv728,bv237,bv761,bv219]]
noncomputable def expected707 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv810,bv6,bv769,bv13,bv219,bv728,bv237,bv761],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv810,bv6,bv769,bv13,bv219,bv728,bv237,bv761]]
theorem structural707 (ops : RootOps19.SourceOps) (b3 b6 b13 b21 b219 b237 b260 b282 b287 b371 b419 b440 b728 b761 b769 b784 b810 b811 b837 b843 b852 b856 b1165 b1181 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h37 : ops.normalization ([2,1],[3]) true false = b282)
    (h38 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h39 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = b287)
    (h41 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = b852)
    (h42 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = b811)
    (h43 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (h44 : ops.normalization ([2,1,1],[3]) true true = b419)
    (h45 : ops.necessary ⟨⟨([1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (h46 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (h47 : ops.necessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (h48 : ops.normalization ([2,1,1,1],[3,1]) false false = b769)
    (h49 : ops.necessary ⟨⟨([1,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [b13])
    (h63 : ops.normalization ([2,1,1,1,1],[3,1]) true false = b219)
    (h64 : ops.necessary ⟨⟨([1,2,1,1,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1,1],[3,1]) = some [b728])
    (h65 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,1],[3,1]) true = b237)
    (h66 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,1],[3,1]) true = b761)
    (h67 : ops.pull (lowerHistoryHN) ([2,1,1,1,1],[3,1]) true = b219)
    : RootOps19.eval ops path707 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b219],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b219]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc4 : lowerHistorySourceChoices ⟨⟨([1,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf4 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path707, h0, h1, h2, h3, h37, h38, h39, h40, h41, h42, h43, h44, h45, h46, h47, h48, h49, h63, h64, h65, h66, h67, hc0, hc1, hc2, hc3, hc4, hf0, hf1, hf2, hf3, hf4, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource707 : lowerHistorySourcePremises path707 = raw707.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural707 RootOps19.actualOps bv3 bv6 bv13 bv21 bv219 bv237 bv260 bv282 bv287 bv371 bv419 bv440 bv728 bv761 bv769 bv784 bv810 bv811 bv837 bv843 bv852 bv856 bv1165 bv1181 op0 op1 op2 op3 op37 op38 op39 op40 op41 op42 op43 op44 op45 op46 op47 op48 op49 op63 op64 op65 op66 op67
theorem dedup707 : raw707.map List.eraseDups = expected707 := by
  decide +kernel
theorem source707 : lowerHistorySourcePremises path707 = expected707 := (rawSource707).trans (dedup707)
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def src707 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,219,728,237,761],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,219,728,237,761]]
theorem sourceIDs707 : lowerHistorySourcePremises path707 = src707.map (List.map lowerHistoryBound) := by
  have hb : src707.map (List.map lowerHistoryBound) = expected707 := by
    simp only [src707, expected707, List.map_cons, List.map_nil, bound3, bound6, bound13, bound21, bound219, bound237, bound260, bound282, bound287, bound371, bound419, bound440, bound728, bound761, bound769, bound784, bound810, bound811, bound837, bound843, bound852, bound856, bound1165, bound1181]
  exact source707.trans hb.symm
theorem length707 : path707.alternatives = (lowerHistorySourcePremises path707).length := by
  rw [sourceIDs707]
  rfl
theorem binding707 : lowerHistoryPathBinding path707 := by
  apply BindingIds19.pathBinding_from_ids path707 src707 [] recs707 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs707 rfl records707 rfl
  · intro r hr _
    simp only [recs707, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise192)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise191)
  · intro r hr _
    simp only [recs707, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path707] using witness698_projection
    · simpa only [blockWids, path707] using witness92_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path707 recs707 records707 length707 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def path708 : LowerHistoryPath := ⟨.mixed,24,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false)],([1,2,1,1],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
noncomputable def raw708 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv270,bv831,bv286,bv846,bv270],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv270,bv831,bv286,bv846,bv270]]
noncomputable def expected708 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv1165,bv419,bv784,bv270,bv831,bv286,bv846],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv287,bv852,bv811,bv1181,bv419,bv784,bv270,bv831,bv286,bv846]]
theorem structural708 (ops : RootOps19.SourceOps) (b3 b21 b260 b270 b282 b286 b287 b371 b419 b440 b784 b811 b831 b837 b843 b846 b852 b856 b1165 b1181 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h37 : ops.normalization ([2,1],[3]) true false = b282)
    (h38 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h39 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (h40 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([2,1],[3]) true = b287)
    (h41 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([2,1],[3]) true = b852)
    (h42 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([2,1],[3]) true = b811)
    (h43 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (h44 : ops.normalization ([2,1,1],[3]) true true = b419)
    (h45 : ops.necessary ⟨⟨([1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (h68 : ops.normalization ([2,1,1],[3,1]) true false = b270)
    (h69 : ops.necessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [b831])
    (h70 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) true = b286)
    (h71 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) true = b846)
    (h72 : ops.pull (lowerHistoryHN) ([2,1,1],[3,1]) true = b270)
    : RootOps19.eval ops path708 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b286,b846,b270],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b286,b846,b270]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path708, h0, h1, h2, h3, h37, h38, h39, h40, h41, h42, h43, h44, h45, h68, h69, h70, h71, h72, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource708 : lowerHistorySourcePremises path708 = raw708.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural708 RootOps19.actualOps bv3 bv21 bv260 bv270 bv282 bv286 bv287 bv371 bv419 bv440 bv784 bv811 bv831 bv837 bv843 bv846 bv852 bv856 bv1165 bv1181 op0 op1 op2 op3 op37 op38 op39 op40 op41 op42 op43 op44 op45 op68 op69 op70 op71 op72
theorem dedup708 : raw708.map List.eraseDups = expected708 := by
  decide +kernel
theorem source708 : lowerHistorySourcePremises path708 = expected708 := (rawSource708).trans (dedup708)
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def extraIDs708 : List (List Nat) := [[836,1139,828,886],[836,1139,279,848,1159,886],[836,1139,279,848,278,882],[836,1139,279,290,437,886],[836,1139,279,290,849,888],[836,259,828,1172],[836,259,279,848,1159,1172],[836,259,279,848,278,1171],[836,259,279,290,437,1172],[836,259,279,290,849,1170],[284,429,828,886],[284,429,279,848,1159,886],[284,429,279,848,278,882],[284,429,279,290,437,886],[284,429,279,290,849,888],[284,819,828,898],[284,819,279,848,1159,898],[284,819,279,848,278,897],[284,819,279,290,437,898],[284,819,279,290,849,899]]
noncomputable def extraExpected708 : List (List CertBound) := [[bv836,bv1139,bv828,bv886],[bv836,bv1139,bv279,bv848,bv1159,bv886],[bv836,bv1139,bv279,bv848,bv278,bv882],[bv836,bv1139,bv279,bv290,bv437,bv886],[bv836,bv1139,bv279,bv290,bv849,bv888],[bv836,bv259,bv828,bv1172],[bv836,bv259,bv279,bv848,bv1159,bv1172],[bv836,bv259,bv279,bv848,bv278,bv1171],[bv836,bv259,bv279,bv290,bv437,bv1172],[bv836,bv259,bv279,bv290,bv849,bv1170],[bv284,bv429,bv828,bv886],[bv284,bv429,bv279,bv848,bv1159,bv886],[bv284,bv429,bv279,bv848,bv278,bv882],[bv284,bv429,bv279,bv290,bv437,bv886],[bv284,bv429,bv279,bv290,bv849,bv888],[bv284,bv819,bv828,bv898],[bv284,bv819,bv279,bv848,bv1159,bv898],[bv284,bv819,bv279,bv848,bv278,bv897],[bv284,bv819,bv279,bv290,bv437,bv898],[bv284,bv819,bv279,bv290,bv849,bv899]]
theorem extraValues708 : (List.range 20).map (BindingIds19.extras path708) = extraExpected708 := by
  decide +kernel
theorem extraIDs_sound708 : (List.range extraIDs708.length).map (BindingIds19.extras path708) = extraIDs708.map (List.map lowerHistoryBound) := by
  have hb : extraIDs708.map (List.map lowerHistoryBound) = extraExpected708 := by
    simp only [extraIDs708, extraExpected708, List.map_cons, List.map_nil, bound259, bound278, bound279, bound284, bound290, bound429, bound437, bound819, bound828, bound836, bound848, bound849, bound882, bound886, bound888, bound897, bound898, bound899, bound1139, bound1159, bound1170, bound1171, bound1172]
  exact extraValues708.trans hb.symm
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def src708 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,270,831,286,846],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,270,831,286,846]]
theorem sourceIDs708 : lowerHistorySourcePremises path708 = src708.map (List.map lowerHistoryBound) := by
  have hb : src708.map (List.map lowerHistoryBound) = expected708 := by
    simp only [src708, expected708, List.map_cons, List.map_nil, bound3, bound21, bound260, bound270, bound282, bound286, bound287, bound371, bound419, bound440, bound784, bound811, bound831, bound837, bound843, bound846, bound852, bound856, bound1165, bound1181]
  exact source708.trans hb.symm
theorem length708 : path708.alternatives = (lowerHistorySourcePremises path708).length := by
  rw [sourceIDs708]
  rfl
theorem binding708 : lowerHistoryPathBinding path708 := by
  apply BindingIds19.pathBinding_from_ids path708 src708 extraIDs708 recs708 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs708 extraIDs_sound708 records708 rfl
  · intro r hr _
    simp only [recs708, List.mem_cons, List.not_mem_nil, or_false] at hr
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
    simp only [recs708, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [blockWids, path708] using witness72_projection
    · simpa only [blockWids, path708] using witness72_projection
    · simpa only [blockWids, path708] using witness28_projection
    · simpa only [blockWids, path708] using witness558_projection
    · simpa only [blockWids, path708] using witness175_projection
    · simpa only [blockWids, path708] using witness76_projection
    · simpa only [blockWids, path708] using witness76_projection
    · simpa only [blockWids, path708] using witness32_projection
    · simpa only [blockWids, path708] using witness562_projection
    · simpa only [blockWids, path708] using witness179_projection
    · simpa only [blockWids, path708] using witness314_projection
    · simpa only [blockWids, path708] using witness314_projection
    · simpa only [blockWids, path708] using witness18_projection
    · simpa only [blockWids, path708] using witness548_projection
    · simpa only [blockWids, path708] using witness165_projection
    · simpa only [blockWids, path708] using witness60_projection
    · simpa only [blockWids, path708] using witness60_projection
    · simpa only [blockWids, path708] using witness22_projection
    · simpa only [blockWids, path708] using witness552_projection
    · simpa only [blockWids, path708] using witness169_projection
    · simpa only [blockWids, path708] using witness155_projection
    · simpa only [blockWids, path708] using witness155_projection
    · simpa only [blockWids, path708] using witness28_projection
    · simpa only [blockWids, path708] using witness558_projection
    · simpa only [blockWids, path708] using witness175_projection
    · simpa only [blockWids, path708] using witness159_projection
    · simpa only [blockWids, path708] using witness159_projection
    · simpa only [blockWids, path708] using witness32_projection
    · simpa only [blockWids, path708] using witness562_projection
    · simpa only [blockWids, path708] using witness179_projection
    · simpa only [blockWids, path708] using witness314_projection
    · simpa only [blockWids, path708] using witness314_projection
    · simpa only [blockWids, path708] using witness18_projection
    · simpa only [blockWids, path708] using witness548_projection
    · simpa only [blockWids, path708] using witness165_projection
    · simpa only [blockWids, path708] using witness113_projection
    · simpa only [blockWids, path708] using witness113_projection
    · simpa only [blockWids, path708] using witness22_projection
    · simpa only [blockWids, path708] using witness552_projection
    · simpa only [blockWids, path708] using witness169_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path708 recs708 records708 length708 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
open BindingNumeric20
theorem op74 : lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1],[3,1]) = some [bv2] := by
  decide +kernel
theorem op75 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([2,1],[3,1]) false = bv1152 := by
  norm_num [bv1152, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op76 : lowerHistoryNormalization ([2,1,3],[3,1]) true true = bv426 := by
  norm_num [bv426, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op77 : lowerHistoryNecessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,3],[3,1]) = some [bv752] := by
  decide +kernel
theorem op78 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,3],[3,1]) true = bv255 := by
  norm_num [bv255, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op79 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,3],[3,1]) true = bv792 := by
  norm_num [bv792, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op80 : lowerHistoryPull (lowerHistoryHN) ([2,1,3],[3,1]) true = bv263 := by
  norm_num [bv263, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op81 : lowerHistoryPull (lowerHistoryH7) ([2,1],[3,1]) false = bv274 := by
  norm_num [bv274, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op82 : lowerHistoryPull (lowerHistoryH9) ([2,1],[3,1]) false = bv878 := by
  norm_num [bv878, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op83 : lowerHistoryNormalization ([2,1,2],[3,1]) true true = bv418 := by
  norm_num [bv418, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op84 : lowerHistoryNecessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,2],[3,1]) = some [bv779] := by
  decide +kernel
theorem op85 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) true = bv266 := by
  norm_num [bv266, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def path709 : LowerHistoryPath := ⟨.mixed,25,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([3],[]),true)],([1,2,1,3],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
noncomputable def raw709 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv851,bv2,bv1152,bv426,bv752,bv255,bv792,bv263]]
noncomputable def expected709 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv851,bv2,bv1152,bv426,bv752,bv255,bv792,bv263]]
theorem structural709 (ops : RootOps19.SourceOps) (b2 b3 b21 b255 b260 b263 b282 b371 b426 b440 b752 b792 b837 b843 b851 b856 b1152 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h37 : ops.normalization ([2,1],[3]) true false = b282)
    (h38 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h73 : ops.normalization ([2,1],[3,1]) false false = b851)
    (h74 : ops.necessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1],[3,1]) = some [b2])
    (h75 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2,1],[3,1]) false = b1152)
    (h76 : ops.normalization ([2,1,3],[3,1]) true true = b426)
    (h77 : ops.necessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,3],[3,1]) = some [b752])
    (h78 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,3],[3,1]) true = b255)
    (h79 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,3],[3,1]) true = b792)
    (h80 : ops.pull (lowerHistoryHN) ([2,1,3],[3,1]) true = b263)
    : RootOps19.eval ops path709 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b851,b2,b1152,b426,b752,b255,b792,b263]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path709, h0, h1, h2, h3, h37, h38, h73, h74, h75, h76, h77, h78, h79, h80, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource709 : lowerHistorySourcePremises path709 = raw709.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural709 RootOps19.actualOps bv2 bv3 bv21 bv255 bv260 bv263 bv282 bv371 bv426 bv440 bv752 bv792 bv837 bv843 bv851 bv856 bv1152 op0 op1 op2 op3 op37 op38 op73 op74 op75 op76 op77 op78 op79 op80
theorem dedup709 : raw709.map List.eraseDups = expected709 := by
  decide +kernel
theorem source709 : lowerHistorySourcePremises path709 = expected709 := (rawSource709).trans (dedup709)
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def src709 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,851,2,1152,426,752,255,792,263]]
theorem sourceIDs709 : lowerHistorySourcePremises path709 = src709.map (List.map lowerHistoryBound) := by
  have hb : src709.map (List.map lowerHistoryBound) = expected709 := by
    simp only [src709, expected709, List.map_cons, List.map_nil, bound2, bound3, bound21, bound255, bound260, bound263, bound282, bound371, bound426, bound440, bound752, bound792, bound837, bound843, bound851, bound856, bound1152]
  exact source709.trans hb.symm
theorem length709 : path709.alternatives = (lowerHistorySourcePremises path709).length := by
  rw [sourceIDs709]
  rfl
theorem binding709 : lowerHistoryPathBinding path709 := by
  apply BindingIds19.pathBinding_from_ids path709 src709 [] recs709 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs709 rfl records709 rfl
  · intro r hr _
    simp only [recs709, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise45)
  · intro r hr _
    simp only [recs709, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path709] using witness746_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path709 recs709 records709 length709 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
open BindingNumeric20
theorem op86 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,2],[3,1]) true = bv813 := by
  norm_num [bv813, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op87 : lowerHistoryPull (lowerHistoryHN) ([2,1,2],[3,1]) true = bv252 := by
  norm_num [bv252, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def path710 : LowerHistoryPath := ⟨.mixed,26,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([2],[]),true)],([1,2,1,2],[3,1,3,1]),(true,false),true,3,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
noncomputable def raw710 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv851,bv2,bv1152,bv418,bv779,bv266,bv813,bv252],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv851,bv2,bv274,bv878,bv418,bv779,bv266,bv813,bv252]]
noncomputable def expected710 : List (List CertBound) := [[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv851,bv2,bv1152,bv418,bv779,bv266,bv813,bv252],[bv371,bv843,bv260,bv440,bv3,bv856,bv21,bv282,bv837,bv851,bv2,bv274,bv878,bv418,bv779,bv266,bv813,bv252]]
theorem structural710 (ops : RootOps19.SourceOps) (b2 b3 b21 b252 b260 b266 b274 b282 b371 b418 b440 b779 b813 b837 b843 b851 b856 b878 b1152 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] = [b371,b843,b260,b440])
    (h1 : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (h2 : ops.normalization ([2],[3]) false false = b856)
    (h3 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (h37 : ops.normalization ([2,1],[3]) true false = b282)
    (h38 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (h73 : ops.normalization ([2,1],[3,1]) false false = b851)
    (h74 : ops.necessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1],[3,1]) = some [b2])
    (h75 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([2,1],[3,1]) false = b1152)
    (h81 : ops.pull (lowerHistoryH7) ([2,1],[3,1]) false = b274)
    (h82 : ops.pull (lowerHistoryH9) ([2,1],[3,1]) false = b878)
    (h83 : ops.normalization ([2,1,2],[3,1]) true true = b418)
    (h84 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,2],[3,1]) = some [b779])
    (h85 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) true = b266)
    (h86 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,2],[3,1]) true = b813)
    (h87 : ops.pull (lowerHistoryHN) ([2,1,2],[3,1]) true = b252)
    : RootOps19.eval ops path710 = ([[b371,b843,b260,b440,b3,b856,b21,b282,b837,b851,b2,b1152,b418,b779,b266,b813,b252],[b371,b843,b260,b440,b3,b856,b21,b282,b837,b851,b2,b274,b878,b418,b779,b266,b813,b252]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path710, h0, h1, h2, h3, h37, h38, h73, h74, h75, h81, h82, h83, h84, h85, h86, h87, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource710 : lowerHistorySourcePremises path710 = raw710.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural710 RootOps19.actualOps bv2 bv3 bv21 bv252 bv260 bv266 bv274 bv282 bv371 bv418 bv440 bv779 bv813 bv837 bv843 bv851 bv856 bv878 bv1152 op0 op1 op2 op3 op37 op38 op73 op74 op75 op81 op82 op83 op84 op85 op86 op87
theorem dedup710 : raw710.map List.eraseDups = expected710 := by
  decide +kernel
theorem source710 : lowerHistorySourcePremises path710 = expected710 := (rawSource710).trans (dedup710)
end M7ContinueSep17.Noninitial20260918.B705_710

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Noninitial20260918.B705_710
noncomputable def src710 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,851,2,1152,418,779,266,813,252],[371,843,260,440,3,856,21,282,837,851,2,274,878,418,779,266,813,252]]
theorem sourceIDs710 : lowerHistorySourcePremises path710 = src710.map (List.map lowerHistoryBound) := by
  have hb : src710.map (List.map lowerHistoryBound) = expected710 := by
    simp only [src710, expected710, List.map_cons, List.map_nil, bound2, bound3, bound21, bound252, bound260, bound266, bound274, bound282, bound371, bound418, bound440, bound779, bound813, bound837, bound843, bound851, bound856, bound878, bound1152]
  exact source710.trans hb.symm
theorem length710 : path710.alternatives = (lowerHistorySourcePremises path710).length := by
  rw [sourceIDs710]
  rfl
theorem binding710 : lowerHistoryPathBinding path710 := by
  apply BindingIds19.pathBinding_from_ids path710 src710 [] recs710 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs710 rfl records710 rfl
  · intro r hr _
    simp only [recs710, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise44)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise43)
  · intro r hr _
    simp only [recs710, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path710] using witness764_projection
    · simpa only [blockWids, path710] using witness764_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path710 recs710 records710 length710 (by decide +kernel)
end M7ContinueSep17.Noninitial20260918.B705_710

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
namespace M7ContinueSep17.Noninitial20260918.B705_710
theorem _root_.solution : lowerHistoryBindingBatch 705 710 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[705]? = some M7ContinueSep17.Noninitial20260918.B705_710.path706 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 21 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding706
  · have hl : lowerHistoryPaths[706]? = some M7ContinueSep17.Noninitial20260918.B705_710.path707 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 22 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding707
  · have hl : lowerHistoryPaths[707]? = some M7ContinueSep17.Noninitial20260918.B705_710.path708 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 23 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding708
  · have hl : lowerHistoryPaths[708]? = some M7ContinueSep17.Noninitial20260918.B705_710.path709 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 24 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding709
  · have hl : lowerHistoryPaths[709]? = some M7ContinueSep17.Noninitial20260918.B705_710.path710 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupM 25 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding710
end M7ContinueSep17.Noninitial20260918.B705_710

#print axioms solution
