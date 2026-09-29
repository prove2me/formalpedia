-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_1310_1315
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-18T06:39:36.156526+00:00
-- url     : https://prove2.me/submissions/030e7765-36bf-4c7f-aeec-ad26e19dc9e8

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
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def bv14 : CertBound := ⟨true,false,⟨⟨(-37/167),(0),(0),(172/3507)⟩,⟨(245/334),(0),(0),(1/2338)⟩,⟨(3/2),(0),(0),(-1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv25 : CertBound := ⟨true,false,⟨⟨(-32469/192694),(74431/578082),(0),(0)⟩,⟨(99/142),(1/142),(0),(0)⟩,⟨(43/59),(-1/177),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv46 : CertBound := ⟨true,false,⟨⟨(-241223/3441122),(183159/3441122),(0),(0)⟩,⟨(345/478),(1/478),(0),(0)⟩,⟨(230/313),(-1/313),(0),(0)⟩,⟨(9/13),(-1/13),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv76 : CertBound := ⟨true,false,⟨⟨(-123/12449),(0),(0),(124/37347)⟩,⟨(307/422),(0),(0),(1/1266)⟩,⟨(91/118),(0),(0),(-1/118)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv79 : CertBound := ⟨true,false,⟨⟨(-73/7802),(0),(0),(63/7802)⟩,⟨(63/94),(0),(0),(1/94)⟩,⟨(125/166),(0),(0),(-1/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv82 : CertBound := ⟨true,false,⟨⟨(-209/25370),(0),(0),(119/25370)⟩,⟨(309/430),(0),(0),(1/430)⟩,⟨(91/118),(0),(0),(-1/118)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv87 : CertBound := ⟨true,false,⟨⟨(-121/21331),(0),(0),(76/21331)⟩,⟨(367/514),(0),(0),(1/514)⟩,⟨(125/166),(0),(0),(-1/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv132 : CertBound := ⟨true,false,⟨⟨(133/21164),(324/5291),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(2),(-1),(0),(0)⟩⟩⟩
noncomputable def bv160 : CertBound := ⟨true,false,⟨⟨(8919606550/555376934281),(292292950/1666130802843),(0),(0)⟩,⟨(27833/38062),(-1/38062),(0),(0)⟩,⟨(3416/4667),(1/14001),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv171 : CertBound := ⟨true,false,⟨⟨(448663/22823450),(64697/11411725),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(355/481),(-1/481),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv190 : CertBound := ⟨true,false,⟨⟨(4440582950/137658725737),(132113350/412976177211),(0),(0)⟩,⟨(4497/6218),(-1/18654),(0),(0)⟩,⟨(5131/7081),(1/7081),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv261 : CertBound := ⟨true,false,⟨⟨(871317/2766500),(-100161/5533000),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(4/13),(1/13),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩⟩⟩
noncomputable def bv301 : CertBound := ⟨true,true,⟨⟨(-37/167),(0),(0),(172/3507)⟩,⟨(245/334),(0),(0),(1/2338)⟩,⟨(3/2),(0),(0),(-1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv302 : CertBound := ⟨true,true,⟨⟨(-211/958),(0),(0),(143/2874)⟩,⟨(699/958),(0),(0),(1/958)⟩,⟨(3/2),(0),(0),(-1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv337 : CertBound := ⟨true,true,⟨⟨(-123/12449),(0),(0),(124/37347)⟩,⟨(307/422),(0),(0),(1/1266)⟩,⟨(91/118),(0),(0),(-1/118)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv341 : CertBound := ⟨true,true,⟨⟨(-209/25370),(0),(0),(119/25370)⟩,⟨(309/430),(0),(0),(1/430)⟩,⟨(91/118),(0),(0),(-1/118)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv346 : CertBound := ⟨true,true,⟨⟨(-121/21331),(0),(0),(76/21331)⟩,⟨(367/514),(0),(0),(1/514)⟩,⟨(125/166),(0),(0),(-1/166)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv371 : CertBound := ⟨true,true,⟨⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv433 : CertBound := ⟨true,true,⟨⟨(729/1024),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
noncomputable def bv443 : CertBound := ⟨false,false,⟨⟨(-23157/4069),(13493/4069),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(230/313),(-1/313),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv449 : CertBound := ⟨false,false,⟨⟨(-19/94),(0),(0),(17/282)⟩,⟨(63/94),(0),(0),(1/94)⟩,⟨(3/2),(0),(0),(-1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv451 : CertBound := ⟨false,false,⟨⟨(-3/17),(0),(0),(4/51)⟩,⟨(19/34),(0),(0),(1/34)⟩,⟨(3/2),(0),(0),(-1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩⟩⟩
noncomputable def bv513 : CertBound := ⟨false,false,⟨⟨(150899/31792319),(337783/95376957),(0),(0)⟩,⟨(1006/1367),(-1/4101),(0),(0)⟩,⟨(17117/23257),(1/23257),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv522 : CertBound := ⟨false,false,⟨⟨(91432/16092479),(163713/16092479),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(1801/2461),(-1/2461),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv523 : CertBound := ⟨false,false,⟨⟨(5164/860509),(12352/860509),(0),(0)⟩,⟨(17117/23257),(1/23257),(0),(0)⟩,⟨(355/481),(-1/481),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv525 : CertBound := ⟨false,false,⟨⟨(1923537/312985058),(1980451/312985058),(0),(0)⟩,⟨(46386/63589),(1/63589),(0),(0)⟩,⟨(1801/2461),(-1/2461),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv551 : CertBound := ⟨false,false,⟨⟨(20669/2046707),(56540/2046707),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(230/313),(-1/313),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv557 : CertBound := ⟨false,false,⟨⟨(41360/3843359),(79409/3843359),(0),(0)⟩,⟨(345/478),(1/478),(0),(0)⟩,⟨(896/1237),(-1/1237),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv577 : CertBound := ⟨false,false,⟨⟨(940665/70927106),(950939/70927106),(0),(0)⟩,⟨(20625/28669),(1/28669),(0),(0)⟩,⟨(896/1237),(-1/1237),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv589 : CertBound := ⟨false,false,⟨⟨(229393050/13712164807),(-72153150/13712164807),(0),(0)⟩,⟨(8219/11173),(1/11173),(0),(0)⟩,⟨(5299/7198),(-1/7198),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv600 : CertBound := ⟨false,false,⟨⟨(36185096000/1844779138911),(1225129000/1844779138911),(0),(0)⟩,⟨(472/647),(1/1941),(0),(0)⟩,⟨(27833/38062),(-1/38062),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv633 : CertBound := ⟨false,false,⟨⟨(4895/183313),(29876/549939),(0),(0)⟩,⟨(345/478),(1/478),(0),(0)⟩,⟨(43/59),(-1/177),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv639 : CertBound := ⟨false,false,⟨⟨(45799950/1642897421),(-14373850/1642897421),(0),(0)⟩,⟨(1614/2207),(1/6621),(0),(0)⟩,⟨(3197/4366),(-1/4366),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv660 : CertBound := ⟨false,false,⟨⟨(17011040000/408506343039),(378041000/408506343039),(0),(0)⟩,⟨(631/877),(1/877),(0),(0)⟩,⟨(4497/6218),(-1/18654),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv688 : CertBound := ⟨false,false,⟨⟨(22948350/413758829),(-7175050/413758829),(0),(0)⟩,⟨(2353/3253),(1/3253),(0),(0)⟩,⟨(541/746),(-1/2238),(0),(0)⟩,⟨(1/2),(1/6),(0),(0)⟩,⟨(9/11),(-1/33),(0),(0)⟩⟩⟩
noncomputable def bv799 : CertBound := ⟨false,false,⟨⟨(371/1100),(-1/220),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩,⟨(125/214),(-1/214),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩⟩⟩
noncomputable def bv839 : CertBound := ⟨false,false,⟨⟨(9/10),(0),(0),(-1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(1/10),(0),(0),(1/10)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv843 : CertBound := ⟨false,false,⟨⟨(1),(0),(0),(0)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩,⟨(-3/2),(0),(0),(1/2)⟩,⟨(-1/2),(0),(0),(1/6)⟩⟩⟩
noncomputable def bv930 : CertBound := ⟨false,true,⟨⟨(83606/40211627),(163463/120634881),(0),(0)⟩,⟨(8219/11173),(1/11173),(0),(0)⟩,⟨(5299/7198),(-1/7198),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv938 : CertBound := ⟨false,true,⟨⟨(50222/14453643),(32717/14453643),(0),(0)⟩,⟨(1614/2207),(1/6621),(0),(0)⟩,⟨(3197/4366),(-1/4366),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv962 : CertBound := ⟨false,true,⟨⟨(25286/3640107),(5487/1213369),(0),(0)⟩,⟨(2353/3253),(1/3253),(0),(0)⟩,⟨(541/746),(-1/2238),(0),(0)⟩,⟨(-1),(1),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv977 : CertBound := ⟨false,true,⟨⟨(3448653850/359750416103),(39612350/359750416103),(0),(0)⟩,⟨(47311/64318),(-1/64318),(0),(0)⟩,⟨(17117/23257),(1/23257),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv996 : CertBound := ⟨false,true,⟨⟨(8919606550/555376934281),(292292950/1666130802843),(0),(0)⟩,⟨(27833/38062),(-1/38062),(0),(0)⟩,⟨(3416/4667),(1/14001),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1009 : CertBound := ⟨false,true,⟨⟨(448663/22823450),(64697/11411725),(0),(0)⟩,⟨(52/73),(1/73),(0),(0)⟩,⟨(355/481),(-1/481),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1018 : CertBound := ⟨false,true,⟨⟨(5150292750/224869782163),(-187922750/224869782163),(0),(0)⟩,⟨(735/1006),(1/1006),(0),(0)⟩,⟨(27833/38062),(-1/38062),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1036 : CertBound := ⟨false,true,⟨⟨(4440582950/137658725737),(132113350/412976177211),(0),(0)⟩,⟨(4497/6218),(-1/18654),(0),(0)⟩,⟨(5131/7081),(1/7081),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1058 : CertBound := ⟨false,true,⟨⟨(831114250/17455011041),(-48868250/17455011041),(0),(0)⟩,⟨(345/478),(1/478),(0),(0)⟩,⟨(4497/6218),(-1/18654),(0),(0)⟩,⟨(22/37),(1/37),(0),(0)⟩,⟨(17/22),(-1/22),(0),(0)⟩⟩⟩
noncomputable def bv1162 : CertBound := ⟨false,true,⟨⟨(225/289),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩,⟨(0),(0),(0),(0)⟩⟩⟩
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
open BindingNumeric20
theorem op0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [bv371,bv843,bv433,bv1162] := by
  decide +kernel
theorem op1 : ([] : List CertBound) = [] := by
  decide +kernel
theorem op16 : lowerHistoryNormalization ([1],[]) false false = bv839 := by
  norm_num [bv839, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op17 : lowerHistoryNecessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [bv132] := by
  decide +kernel
theorem op18 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = bv799 := by
  norm_num [bv799, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op19 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = bv261 := by
  norm_num [bv261, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op35 : lowerHistoryNormalization ([1,2],[1]) false false = bv451 := by
  norm_num [bv451, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op36 : lowerHistoryNecessary ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1,2],[1]) = some [bv25] := by
  decide +kernel
theorem op56 : lowerHistoryNormalization ([1,2,1],[1]) false false = bv449 := by
  norm_num [bv449, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op57 : lowerHistoryNecessary ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,2,1],[1]) = some [bv46] := by
  decide +kernel
theorem op60 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH7)) ([1,2,1],[1]) false = bv1009 := by
  norm_num [bv1009, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op61 : lowerHistoryNormalization ([1,2,1,3],[1]) true true = bv302 := by
  norm_num [bv302, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
open BindingNumeric20
theorem op62 : lowerHistoryNecessary ⟨⟨([3,1,2,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,2,1,3],[1]) = some [bv523] := by
  decide +kernel
theorem op66 : lowerHistoryPull (lowerHistoryH2) ([1,2,1,3],[1]) true = bv977 := by
  norm_num [bv977, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op67 : lowerHistoryNormalization ([1,2,1,3,1],[1]) true true = bv301 := by
  norm_num [bv301, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op68 : lowerHistoryNecessary ⟨⟨([3,1,2,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,2,1,3,1],[1]) = some [bv513] := by
  decide +kernel
theorem op69 : lowerHistoryPull (lowerHistoryH7) ([1,2,1,3,1],[1]) true = bv589 := by
  norm_num [bv589, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op70 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,2,1,3,1],[1]) true = bv930 := by
  norm_num [bv930, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op71 : lowerHistoryPull (lowerHistoryHN) ([1,2,1,3,1],[1]) true = bv14 := by
  norm_num [bv14, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op58 : lowerHistoryPull (lowerHistoryH7) ([1,2,1],[1]) false = bv171 := by
  norm_num [bv171, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op72 : lowerHistoryPull (lowerHistoryH9) ([1,2,1],[1]) false = bv443 := by
  norm_num [bv443, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op73 : lowerHistoryNormalization ([1,2,1,2],[1]) true true = bv341 := by
  norm_num [bv341, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op74 : lowerHistoryNecessary ⟨⟨([3,1,2,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,2,1,2],[1]) = some [bv551] := by
  decide +kernel
theorem op75 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,2,1,2],[1]) true = bv160 := by
  norm_num [bv160, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def path1311 : LowerHistoryPath := ⟨.initial,225,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1311 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv1009,bv302,bv523,bv977,bv301,bv513,bv589,bv930,bv14]]
noncomputable def expected1311 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv1009,bv302,bv523,bv977,bv301,bv513,bv589,bv930,bv14]]
theorem structural1311 (ops : RootOps19.SourceOps) (b14 b25 b46 b132 b261 b301 b302 b371 b433 b449 b451 b513 b523 b589 b799 b839 b843 b930 b977 b1009 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h16 : ops.normalization ([1],[]) false false = b839)
    (h17 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h18 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = b799)
    (h19 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = b261)
    (h35 : ops.normalization ([1,2],[1]) false false = b451)
    (h36 : ops.necessary ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1,2],[1]) = some [b25])
    (h56 : ops.normalization ([1,2,1],[1]) false false = b449)
    (h57 : ops.necessary ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,2,1],[1]) = some [b46])
    (h60 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,2,1],[1]) false = b1009)
    (h61 : ops.normalization ([1,2,1,3],[1]) true true = b302)
    (h62 : ops.necessary ⟨⟨([3,1,2,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([1,2,1,3],[1]) = some [b523])
    (h66 : ops.pull (lowerHistoryH2) ([1,2,1,3],[1]) true = b977)
    (h67 : ops.normalization ([1,2,1,3,1],[1]) true true = b301)
    (h68 : ops.necessary ⟨⟨([3,1,2,1,3,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,2,1,3,1],[1]) = some [b513])
    (h69 : ops.pull (lowerHistoryH7) ([1,2,1,3,1],[1]) true = b589)
    (h70 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,2,1,3,1],[1]) true = b930)
    (h71 : ops.pull (lowerHistoryHN) ([1,2,1,3,1],[1]) true = b14)
    : RootOps19.eval ops path1311 = ([[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b1009,b302,b523,b977,b301,b513,b589,b930,b14]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([2],[1]) = [[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[(lowerHistoryComplement lowerHistoryH7)]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,2,1,3],[3,1,3,1]),(false,true)⟩,true,true,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([3],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1311, h0, h1, h16, h17, h18, h19, h35, h36, h56, h57, h60, h61, h62, h66, h67, h68, h69, h70, h71, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1311 : lowerHistorySourcePremises path1311 = raw1311.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1311 RootOps19.actualOps bv14 bv25 bv46 bv132 bv261 bv301 bv302 bv371 bv433 bv449 bv451 bv513 bv523 bv589 bv799 bv839 bv843 bv930 bv977 bv1009 bv1162 op0 op1 op16 op17 op18 op19 op35 op36 op56 op57 op60 op61 op62 op66 op67 op68 op69 op70 op71
theorem dedup1311 : raw1311.map List.eraseDups = expected1311 := by
  decide +kernel
theorem source1311 : lowerHistorySourcePremises path1311 = expected1311 := (rawSource1311).trans (dedup1311)
end M7ContinueSep17.Initial20260918.B1310_1315

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
namespace M7ContinueSep17.Initial20260918.B1310_1315
theorem bound14 : lowerHistoryBound 14 = bv14 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[13]? = some bv14 := Eq.refl (some bv14)
  exact (BoundCompact16.global_to_chunk1 13 (by decide)).trans hl
theorem bound25 : lowerHistoryBound 25 = bv25 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[24]? = some bv25 := Eq.refl (some bv25)
  exact (BoundCompact16.global_to_chunk1 24 (by decide)).trans hl
theorem bound46 : lowerHistoryBound 46 = bv46 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[45]? = some bv46 := Eq.refl (some bv46)
  exact (BoundCompact16.global_to_chunk1 45 (by decide)).trans hl
theorem bound76 : lowerHistoryBound 76 = bv76 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[75]? = some bv76 := Eq.refl (some bv76)
  exact (BoundCompact16.global_to_chunk1 75 (by decide)).trans hl
theorem bound79 : lowerHistoryBound 79 = bv79 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[78]? = some bv79 := Eq.refl (some bv79)
  exact (BoundCompact16.global_to_chunk1 78 (by decide)).trans hl
theorem bound82 : lowerHistoryBound 82 = bv82 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[81]? = some bv82 := Eq.refl (some bv82)
  exact (BoundCompact16.global_to_chunk1 81 (by decide)).trans hl
theorem bound87 : lowerHistoryBound 87 = bv87 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[86]? = some bv87 := Eq.refl (some bv87)
  exact (BoundCompact16.global_to_chunk1 86 (by decide)).trans hl
theorem bound132 : lowerHistoryBound 132 = bv132 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[131]? = some bv132 := Eq.refl (some bv132)
  exact (BoundCompact16.global_to_chunk1 131 (by decide)).trans hl
theorem bound160 : lowerHistoryBound 160 = bv160 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[159]? = some bv160 := Eq.refl (some bv160)
  exact (BoundCompact16.global_to_chunk1 159 (by decide)).trans hl
theorem bound171 : lowerHistoryBound 171 = bv171 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[170]? = some bv171 := Eq.refl (some bv171)
  exact (BoundCompact16.global_to_chunk1 170 (by decide)).trans hl
theorem bound190 : lowerHistoryBound 190 = bv190 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds01[189]? = some bv190 := Eq.refl (some bv190)
  exact (BoundCompact16.global_to_chunk1 189 (by decide)).trans hl
theorem bound261 : lowerHistoryBound 261 = bv261 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[60]? = some bv261 := Eq.refl (some bv261)
  exact (BoundCompact16.global_to_chunk2 60 (by decide)).trans hl
theorem bound301 : lowerHistoryBound 301 = bv301 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[100]? = some bv301 := Eq.refl (some bv301)
  exact (BoundCompact16.global_to_chunk2 100 (by decide)).trans hl
theorem bound302 : lowerHistoryBound 302 = bv302 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[101]? = some bv302 := Eq.refl (some bv302)
  exact (BoundCompact16.global_to_chunk2 101 (by decide)).trans hl
theorem bound337 : lowerHistoryBound 337 = bv337 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[136]? = some bv337 := Eq.refl (some bv337)
  exact (BoundCompact16.global_to_chunk2 136 (by decide)).trans hl
theorem bound341 : lowerHistoryBound 341 = bv341 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[140]? = some bv341 := Eq.refl (some bv341)
  exact (BoundCompact16.global_to_chunk2 140 (by decide)).trans hl
theorem bound346 : lowerHistoryBound 346 = bv346 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[145]? = some bv346 := Eq.refl (some bv346)
  exact (BoundCompact16.global_to_chunk2 145 (by decide)).trans hl
theorem bound371 : lowerHistoryBound 371 = bv371 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds02[170]? = some bv371 := Eq.refl (some bv371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hl
theorem bound433 : lowerHistoryBound 433 = bv433 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[32]? = some bv433 := Eq.refl (some bv433)
  exact (BoundCompact16.global_to_chunk3 32 (by decide)).trans hl
theorem bound443 : lowerHistoryBound 443 = bv443 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[42]? = some bv443 := Eq.refl (some bv443)
  exact (BoundCompact16.global_to_chunk3 42 (by decide)).trans hl
theorem bound449 : lowerHistoryBound 449 = bv449 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[48]? = some bv449 := Eq.refl (some bv449)
  exact (BoundCompact16.global_to_chunk3 48 (by decide)).trans hl
theorem bound451 : lowerHistoryBound 451 = bv451 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[50]? = some bv451 := Eq.refl (some bv451)
  exact (BoundCompact16.global_to_chunk3 50 (by decide)).trans hl
theorem bound513 : lowerHistoryBound 513 = bv513 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[112]? = some bv513 := Eq.refl (some bv513)
  exact (BoundCompact16.global_to_chunk3 112 (by decide)).trans hl
theorem bound522 : lowerHistoryBound 522 = bv522 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[121]? = some bv522 := Eq.refl (some bv522)
  exact (BoundCompact16.global_to_chunk3 121 (by decide)).trans hl
theorem bound523 : lowerHistoryBound 523 = bv523 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[122]? = some bv523 := Eq.refl (some bv523)
  exact (BoundCompact16.global_to_chunk3 122 (by decide)).trans hl
theorem bound525 : lowerHistoryBound 525 = bv525 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[124]? = some bv525 := Eq.refl (some bv525)
  exact (BoundCompact16.global_to_chunk3 124 (by decide)).trans hl
theorem bound551 : lowerHistoryBound 551 = bv551 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[150]? = some bv551 := Eq.refl (some bv551)
  exact (BoundCompact16.global_to_chunk3 150 (by decide)).trans hl
theorem bound557 : lowerHistoryBound 557 = bv557 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[156]? = some bv557 := Eq.refl (some bv557)
  exact (BoundCompact16.global_to_chunk3 156 (by decide)).trans hl
theorem bound577 : lowerHistoryBound 577 = bv577 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[176]? = some bv577 := Eq.refl (some bv577)
  exact (BoundCompact16.global_to_chunk3 176 (by decide)).trans hl
theorem bound589 : lowerHistoryBound 589 = bv589 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[188]? = some bv589 := Eq.refl (some bv589)
  exact (BoundCompact16.global_to_chunk3 188 (by decide)).trans hl
theorem bound600 : lowerHistoryBound 600 = bv600 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds03[199]? = some bv600 := Eq.refl (some bv600)
  exact (BoundCompact16.global_to_chunk3 199 (by decide)).trans hl
theorem bound633 : lowerHistoryBound 633 = bv633 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[32]? = some bv633 := Eq.refl (some bv633)
  exact (BoundCompact16.global_to_chunk4 32 (by decide)).trans hl
theorem bound639 : lowerHistoryBound 639 = bv639 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[38]? = some bv639 := Eq.refl (some bv639)
  exact (BoundCompact16.global_to_chunk4 38 (by decide)).trans hl
theorem bound660 : lowerHistoryBound 660 = bv660 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[59]? = some bv660 := Eq.refl (some bv660)
  exact (BoundCompact16.global_to_chunk4 59 (by decide)).trans hl
theorem bound688 : lowerHistoryBound 688 = bv688 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[87]? = some bv688 := Eq.refl (some bv688)
  exact (BoundCompact16.global_to_chunk4 87 (by decide)).trans hl
theorem bound799 : lowerHistoryBound 799 = bv799 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds04[198]? = some bv799 := Eq.refl (some bv799)
  exact (BoundCompact16.global_to_chunk4 198 (by decide)).trans hl
theorem bound839 : lowerHistoryBound 839 = bv839 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[38]? = some bv839 := Eq.refl (some bv839)
  exact (BoundCompact16.global_to_chunk5 38 (by decide)).trans hl
theorem bound843 : lowerHistoryBound 843 = bv843 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[42]? = some bv843 := Eq.refl (some bv843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hl
theorem bound930 : lowerHistoryBound 930 = bv930 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[129]? = some bv930 := Eq.refl (some bv930)
  exact (BoundCompact16.global_to_chunk5 129 (by decide)).trans hl
theorem bound938 : lowerHistoryBound 938 = bv938 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[137]? = some bv938 := Eq.refl (some bv938)
  exact (BoundCompact16.global_to_chunk5 137 (by decide)).trans hl
theorem bound962 : lowerHistoryBound 962 = bv962 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[161]? = some bv962 := Eq.refl (some bv962)
  exact (BoundCompact16.global_to_chunk5 161 (by decide)).trans hl
theorem bound977 : lowerHistoryBound 977 = bv977 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[176]? = some bv977 := Eq.refl (some bv977)
  exact (BoundCompact16.global_to_chunk5 176 (by decide)).trans hl
theorem bound996 : lowerHistoryBound 996 = bv996 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds05[195]? = some bv996 := Eq.refl (some bv996)
  exact (BoundCompact16.global_to_chunk5 195 (by decide)).trans hl
theorem bound1009 : lowerHistoryBound 1009 = bv1009 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[8]? = some bv1009 := Eq.refl (some bv1009)
  exact (BoundCompact16.global_to_chunk6 8).trans hl
theorem bound1018 : lowerHistoryBound 1018 = bv1018 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[17]? = some bv1018 := Eq.refl (some bv1018)
  exact (BoundCompact16.global_to_chunk6 17).trans hl
theorem bound1036 : lowerHistoryBound 1036 = bv1036 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[35]? = some bv1036 := Eq.refl (some bv1036)
  exact (BoundCompact16.global_to_chunk6 35).trans hl
theorem bound1058 : lowerHistoryBound 1058 = bv1058 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[57]? = some bv1058 := Eq.refl (some bv1058)
  exact (BoundCompact16.global_to_chunk6 57).trans hl
theorem bound1162 : lowerHistoryBound 1162 = bv1162 := by
  apply BoundCompact16.bound_of_option
  have hl : lowerHistoryBounds06[161]? = some bv1162 := Eq.refl (some bv1162)
  exact (BoundCompact16.global_to_chunk6 161).trans hl
end M7ContinueSep17.Initial20260918.B1310_1315

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
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def recs1311 : List LowerHistoryRecord := [⟨.initial,225,0,(-1),false,661,452⟩]
theorem records1311 : lowerHistoryRecordsFor (⟨.initial,225,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,1,3,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1311 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 225)) = recs1311
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1312 : List LowerHistoryRecord := [⟨.initial,226,0,(-1),false,760,374⟩,⟨.initial,226,1,(-1),false,758,374⟩]
theorem records1312 : lowerHistoryRecordsFor (⟨.initial,226,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,2,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1312 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 226)) = recs1312
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1313 : List LowerHistoryRecord := [⟨.initial,227,0,(-1),false,750,459⟩,⟨.initial,227,1,(-1),false,746,459⟩,⟨.initial,227,2,(-1),false,748,459⟩,⟨.initial,227,3,(-1),false,744,459⟩]
theorem records1313 : lowerHistoryRecordsFor (⟨.initial,227,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,2,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,4⟩ : LowerHistoryPath) = recs1313 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 227)) = recs1313
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1314 : List LowerHistoryRecord := [⟨.initial,228,0,(-1),false,756,391⟩]
theorem records1314 : lowerHistoryRecordsFor (⟨.initial,228,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,2,1,1],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩ : LowerHistoryPath) = recs1314 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 228)) = recs1314
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
noncomputable def recs1315 : List LowerHistoryRecord := [⟨.initial,229,0,(-1),false,754,477⟩,⟨.initial,229,1,(-1),false,752,477⟩]
theorem records1315 : lowerHistoryRecordsFor (⟨.initial,229,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩ : LowerHistoryPath) = recs1315 := by
  rw [M7ContinueSep17.CatalogueGeneral.records_for_catalog]
  change (M7ContinueSep17.CatalogueGeneral.catalogRecords .initial).filter (fun r => decide (r.catalog = .initial ∧ r.pathId = 229)) = recs1315
  rw [M7ContinueSep17.CatalogueGeneral.catalogListH]
  rfl
end M7ContinueSep17.Initial20260918.B1310_1315

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
namespace M7ContinueSep17.Initial20260918.B1310_1315
theorem premise661 : lowerHistoryPremises[660]? = some ([14,25,46,132,261,301,302,371,433,449,451,513,523,589,799,839,843,930,977,1009,1162] : List Nat) := by
  have hg : lowerHistoryPremises[660]? = lowerHistoryPremises04[60]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 60 (by decide)
  exact hg.trans (by rfl)
theorem premise744 : lowerHistoryPremises[743]? = some ([25,46,76,132,160,171,261,337,341,371,433,443,449,451,522,525,551,600,639,799,839,843,938,1018,1162] : List Nat) := by
  have hg : lowerHistoryPremises[743]? = lowerHistoryPremises04[143]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 143 (by decide)
  exact hg.trans (by rfl)
theorem premise746 : lowerHistoryPremises[745]? = some ([25,46,76,132,160,261,337,341,371,433,449,451,522,525,551,600,639,799,839,843,938,1009,1018,1162] : List Nat) := by
  have hg : lowerHistoryPremises[745]? = lowerHistoryPremises04[145]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 145 (by decide)
  exact hg.trans (by rfl)
theorem premise748 : lowerHistoryPremises[747]? = some ([25,46,76,132,171,261,337,341,371,433,443,449,451,522,551,639,799,839,843,938,996,1162] : List Nat) := by
  have hg : lowerHistoryPremises[747]? = lowerHistoryPremises04[147]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 147 (by decide)
  exact hg.trans (by rfl)
theorem premise750 : lowerHistoryPremises[749]? = some ([25,46,76,132,261,337,341,371,433,449,451,522,551,639,799,839,843,938,996,1009,1162] : List Nat) := by
  have hg : lowerHistoryPremises[749]? = lowerHistoryPremises04[149]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 149 (by decide)
  exact hg.trans (by rfl)
theorem premise752 : lowerHistoryPremises[751]? = some ([25,46,79,87,132,190,261,346,371,433,449,451,557,577,633,660,688,799,839,843,962,1058,1162] : List Nat) := by
  have hg : lowerHistoryPremises[751]? = lowerHistoryPremises04[151]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 151 (by decide)
  exact hg.trans (by rfl)
theorem premise754 : lowerHistoryPremises[753]? = some ([25,46,79,87,132,261,346,371,433,449,451,557,633,688,799,839,843,962,1036,1162] : List Nat) := by
  have hg : lowerHistoryPremises[753]? = lowerHistoryPremises04[153]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 153 (by decide)
  exact hg.trans (by rfl)
theorem premise756 : lowerHistoryPremises[755]? = some ([25,46,79,132,190,261,371,433,449,451,633,660,799,839,843,1162] : List Nat) := by
  have hg : lowerHistoryPremises[755]? = lowerHistoryPremises04[155]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 155 (by decide)
  exact hg.trans (by rfl)
theorem premise758 : lowerHistoryPremises[757]? = some ([25,46,82,132,160,171,261,341,371,433,443,449,451,551,600,799,839,843,1162] : List Nat) := by
  have hg : lowerHistoryPremises[757]? = lowerHistoryPremises04[157]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 157 (by decide)
  exact hg.trans (by rfl)
theorem premise760 : lowerHistoryPremises[759]? = some ([25,46,82,132,160,261,341,371,433,449,451,551,600,799,839,843,1009,1162] : List Nat) := by
  have hg : lowerHistoryPremises[759]? = lowerHistoryPremises04[159]? := by
    unfold lowerHistoryPremises
    exact M7ContinueSep17.Finish50.Six.lookup_chunk4 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 M7SplitSep17.preSize1 M7SplitSep17.preSize2 M7SplitSep17.preSize3 M7SplitSep17.preSize4 M7SplitSep17.preSize5 159 (by decide)
  exact hg.trans (by rfl)
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
attribute [local irreducible] Freiman.lowerHistoryBound
namespace M7ContinueSep17.Initial20260918.B1310_1315
theorem witness374_projection : (lowerHistoryWitness 374).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 374).upperBound = lowerHistoryBound 600 ∧ (lowerHistoryWitness 374).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[173]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 600, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 600, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[373]? = lowerHistoryWitnesses02[173]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 173 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness391_projection : (lowerHistoryWitness 391).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 391).upperBound = lowerHistoryBound 660 ∧ (lowerHistoryWitness 391).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[190]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 660, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 660, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[390]? = lowerHistoryWitnesses02[190]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk2 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 190 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness452_projection : (lowerHistoryWitness 452).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 452).upperBound = lowerHistoryBound 930 ∧ (lowerHistoryWitness 452).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[51]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 930, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 930, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[451]? = lowerHistoryWitnesses03[51]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 51 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness459_projection : (lowerHistoryWitness 459).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 459).upperBound = lowerHistoryBound 938 ∧ (lowerHistoryWitness 459).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[58]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 938, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 938, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[458]? = lowerHistoryWitnesses03[58]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 58 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
theorem witness477_projection : (lowerHistoryWitness 477).lowerBound = lowerHistoryBound 433 ∧ (lowerHistoryWitness 477).upperBound = lowerHistoryBound 962 ∧ (lowerHistoryWitness 477).rectangle = (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses03[76]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 433, lowerHistoryBound 962, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 433, lowerHistoryBound 962, (⟨(1/4),(1/3),(5/19),(4/15)⟩ : CertRectangle)))
  have hg : lowerHistoryWitnesses[476]? = lowerHistoryWitnesses03[76]? := by
    unfold lowerHistoryWitnesses
    exact M7ContinueSep17.Finish50.Six.lookup_chunk3 lowerHistoryWitnesses01 lowerHistoryWitnesses02 lowerHistoryWitnesses03 lowerHistoryWitnesses04 lowerHistoryWitnesses05 lowerHistoryWitnesses06 WitnessCompact16.size01 WitnessCompact16.size02 WitnessCompact16.size03 WitnessCompact16.size04 WitnessCompact16.size05 76 (by decide)
  exact (congrArg (Option.map WitnessCompact16.witnessShape) hg).trans hl
noncomputable def blockWids : Nat → Nat × Nat
  | 374 => (433,600)
  | 391 => (433,660)
  | 452 => (433,930)
  | 459 => (433,938)
  | 477 => (433,962)
  | _ => (0,0)
noncomputable def blockPreIDs : Nat → List Nat
  | 661 => [14,25,46,132,261,301,302,371,433,449,451,513,523,589,799,839,843,930,977,1009,1162]
  | 744 => [25,46,76,132,160,171,261,337,341,371,433,443,449,451,522,525,551,600,639,799,839,843,938,1018,1162]
  | 746 => [25,46,76,132,160,261,337,341,371,433,449,451,522,525,551,600,639,799,839,843,938,1009,1018,1162]
  | 748 => [25,46,76,132,171,261,337,341,371,433,443,449,451,522,551,639,799,839,843,938,996,1162]
  | 750 => [25,46,76,132,261,337,341,371,433,449,451,522,551,639,799,839,843,938,996,1009,1162]
  | 752 => [25,46,79,87,132,190,261,346,371,433,449,451,557,577,633,660,688,799,839,843,962,1058,1162]
  | 754 => [25,46,79,87,132,261,346,371,433,449,451,557,633,688,799,839,843,962,1036,1162]
  | 756 => [25,46,79,132,190,261,371,433,449,451,633,660,799,839,843,1162]
  | 758 => [25,46,82,132,160,171,261,341,371,433,443,449,451,551,600,799,839,843,1162]
  | 760 => [25,46,82,132,160,261,341,371,433,449,451,551,600,799,839,843,1009,1162]
  | _ => []
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def src1311 : List (List Nat) := [[371,843,433,1162,839,132,799,261,451,25,449,46,1009,302,523,977,301,513,589,930,14]]
theorem sourceIDs1311 : lowerHistorySourcePremises path1311 = src1311.map (List.map lowerHistoryBound) := by
  have hb : src1311.map (List.map lowerHistoryBound) = expected1311 := by
    simp only [src1311, expected1311, List.map_cons, List.map_nil, bound14, bound25, bound46, bound132, bound261, bound301, bound302, bound371, bound433, bound449, bound451, bound513, bound523, bound589, bound799, bound839, bound843, bound930, bound977, bound1009, bound1162]
  exact source1311.trans hb.symm
theorem length1311 : path1311.alternatives = (lowerHistorySourcePremises path1311).length := by
  rw [sourceIDs1311]
  rfl
theorem binding1311 : lowerHistoryPathBinding path1311 := by
  apply BindingIds19.pathBinding_from_ids path1311 src1311 [] recs1311 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1311 rfl records1311 rfl
  · intro r hr _
    simp only [recs1311, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise661)
  · intro r hr _
    simp only [recs1311, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1311] using witness452_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1311 recs1311 records1311 length1311 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
open BindingNumeric20
theorem op76 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,2,1,2],[1]) true = bv600 := by
  norm_num [bv600, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op77 : lowerHistoryPull (lowerHistoryHN) ([1,2,1,2],[1]) true = bv82 := by
  norm_num [bv82, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op78 : lowerHistoryPull (lowerHistoryH2) ([1,2,1,2],[1]) true = bv996 := by
  norm_num [bv996, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op79 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,2,1,2],[1]) true = bv160 := by
  norm_num [bv160, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op80 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,2,1,2],[1]) true = bv600 := by
  norm_num [bv600, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op81 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,2,1,2],[1]) true = bv525 := by
  norm_num [bv525, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op82 : lowerHistoryPull (lowerHistoryH23) ([1,2,1,2],[1]) true = bv1018 := by
  norm_num [bv1018, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op83 : lowerHistoryNormalization ([1,2,1,2,1],[1]) true true = bv337 := by
  norm_num [bv337, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op84 : lowerHistoryNecessary ⟨⟨([3,1,2,1,2,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,2,1,2,1],[1]) = some [bv522] := by
  decide +kernel
theorem op85 : lowerHistoryPull (lowerHistoryH7) ([1,2,1,2,1],[1]) true = bv639 := by
  norm_num [bv639, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op86 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,2,1,2,1],[1]) true = bv938 := by
  norm_num [bv938, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op87 : lowerHistoryPull (lowerHistoryHN) ([1,2,1,2,1],[1]) true = bv76 := by
  norm_num [bv76, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def path1312 : LowerHistoryPath := ⟨.initial,226,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,2,1,2],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩
noncomputable def raw1312 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv1009,bv341,bv551,bv160,bv600,bv82],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv171,bv443,bv341,bv551,bv160,bv600,bv82]]
noncomputable def expected1312 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv1009,bv341,bv551,bv160,bv600,bv82],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv171,bv443,bv341,bv551,bv160,bv600,bv82]]
theorem structural1312 (ops : RootOps19.SourceOps) (b25 b46 b82 b132 b160 b171 b261 b341 b371 b433 b443 b449 b451 b551 b600 b799 b839 b843 b1009 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h16 : ops.normalization ([1],[]) false false = b839)
    (h17 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h18 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = b799)
    (h19 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = b261)
    (h35 : ops.normalization ([1,2],[1]) false false = b451)
    (h36 : ops.necessary ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1,2],[1]) = some [b25])
    (h56 : ops.normalization ([1,2,1],[1]) false false = b449)
    (h57 : ops.necessary ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,2,1],[1]) = some [b46])
    (h60 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,2,1],[1]) false = b1009)
    (h58 : ops.pull (lowerHistoryH7) ([1,2,1],[1]) false = b171)
    (h72 : ops.pull (lowerHistoryH9) ([1,2,1],[1]) false = b443)
    (h73 : ops.normalization ([1,2,1,2],[1]) true true = b341)
    (h74 : ops.necessary ⟨⟨([3,1,2,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,2,1,2],[1]) = some [b551])
    (h75 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,2,1,2],[1]) true = b160)
    (h76 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,2,1,2],[1]) true = b600)
    (h77 : ops.pull (lowerHistoryHN) ([1,2,1,2],[1]) true = b82)
    : RootOps19.eval ops path1312 = ([[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b1009,b341,b551,b160,b600,b82],[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b171,b443,b341,b551,b160,b600,b82]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([2],[1]) = [[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1312, h0, h1, h16, h17, h18, h19, h35, h36, h56, h57, h60, h58, h72, h73, h74, h75, h76, h77, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1312 : lowerHistorySourcePremises path1312 = raw1312.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1312 RootOps19.actualOps bv25 bv46 bv82 bv132 bv160 bv171 bv261 bv341 bv371 bv433 bv443 bv449 bv451 bv551 bv600 bv799 bv839 bv843 bv1009 bv1162 op0 op1 op16 op17 op18 op19 op35 op36 op56 op57 op60 op58 op72 op73 op74 op75 op76 op77
theorem dedup1312 : raw1312.map List.eraseDups = expected1312 := by
  decide +kernel
theorem source1312 : lowerHistorySourcePremises path1312 = expected1312 := (rawSource1312).trans (dedup1312)
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def src1312 : List (List Nat) := [[371,843,433,1162,839,132,799,261,451,25,449,46,1009,341,551,160,600,82],[371,843,433,1162,839,132,799,261,451,25,449,46,171,443,341,551,160,600,82]]
theorem sourceIDs1312 : lowerHistorySourcePremises path1312 = src1312.map (List.map lowerHistoryBound) := by
  have hb : src1312.map (List.map lowerHistoryBound) = expected1312 := by
    simp only [src1312, expected1312, List.map_cons, List.map_nil, bound25, bound46, bound82, bound132, bound160, bound171, bound261, bound341, bound371, bound433, bound443, bound449, bound451, bound551, bound600, bound799, bound839, bound843, bound1009, bound1162]
  exact source1312.trans hb.symm
theorem length1312 : path1312.alternatives = (lowerHistorySourcePremises path1312).length := by
  rw [sourceIDs1312]
  rfl
theorem binding1312 : lowerHistoryPathBinding path1312 := by
  apply BindingIds19.pathBinding_from_ids path1312 src1312 [] recs1312 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1312 rfl records1312 rfl
  · intro r hr _
    simp only [recs1312, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise760)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise758)
  · intro r hr _
    simp only [recs1312, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1312] using witness374_projection
    · simpa only [blockWids, path1312] using witness374_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1312 recs1312 records1312 length1312 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def path1313 : LowerHistoryPath := ⟨.initial,227,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,2,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,4⟩
noncomputable def raw1313 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv1009,bv341,bv551,bv996,bv337,bv522,bv639,bv938,bv76],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv1009,bv341,bv551,bv160,bv600,bv525,bv1018,bv337,bv522,bv639,bv938,bv76],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv171,bv443,bv341,bv551,bv996,bv337,bv522,bv639,bv938,bv76],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv171,bv443,bv341,bv551,bv160,bv600,bv525,bv1018,bv337,bv522,bv639,bv938,bv76]]
noncomputable def expected1313 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv1009,bv341,bv551,bv996,bv337,bv522,bv639,bv938,bv76],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv1009,bv341,bv551,bv160,bv600,bv525,bv1018,bv337,bv522,bv639,bv938,bv76],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv171,bv443,bv341,bv551,bv996,bv337,bv522,bv639,bv938,bv76],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv171,bv443,bv341,bv551,bv160,bv600,bv525,bv1018,bv337,bv522,bv639,bv938,bv76]]
theorem structural1313 (ops : RootOps19.SourceOps) (b25 b46 b76 b132 b160 b171 b261 b337 b341 b371 b433 b443 b449 b451 b522 b525 b551 b600 b639 b799 b839 b843 b938 b996 b1009 b1018 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h16 : ops.normalization ([1],[]) false false = b839)
    (h17 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h18 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = b799)
    (h19 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = b261)
    (h35 : ops.normalization ([1,2],[1]) false false = b451)
    (h36 : ops.necessary ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1,2],[1]) = some [b25])
    (h56 : ops.normalization ([1,2,1],[1]) false false = b449)
    (h57 : ops.necessary ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,2,1],[1]) = some [b46])
    (h60 : ops.pull ((lowerHistoryComplement lowerHistoryH7)) ([1,2,1],[1]) false = b1009)
    (h58 : ops.pull (lowerHistoryH7) ([1,2,1],[1]) false = b171)
    (h72 : ops.pull (lowerHistoryH9) ([1,2,1],[1]) false = b443)
    (h73 : ops.normalization ([1,2,1,2],[1]) true true = b341)
    (h74 : ops.necessary ⟨⟨([3,1,2,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([1,2,1,2],[1]) = some [b551])
    (h78 : ops.pull (lowerHistoryH2) ([1,2,1,2],[1]) true = b996)
    (h79 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,2,1,2],[1]) true = b160)
    (h80 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,2,1,2],[1]) true = b600)
    (h81 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,2,1,2],[1]) true = b525)
    (h82 : ops.pull (lowerHistoryH23) ([1,2,1,2],[1]) true = b1018)
    (h83 : ops.normalization ([1,2,1,2,1],[1]) true true = b337)
    (h84 : ops.necessary ⟨⟨([3,1,2,1,2,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,2,1,2,1],[1]) = some [b522])
    (h85 : ops.pull (lowerHistoryH7) ([1,2,1,2,1],[1]) true = b639)
    (h86 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,2,1,2,1],[1]) true = b938)
    (h87 : ops.pull (lowerHistoryHN) ([1,2,1,2,1],[1]) true = b76)
    : RootOps19.eval ops path1313 = ([[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b1009,b341,b551,b996,b337,b522,b639,b938,b76],[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b1009,b341,b551,b160,b600,b525,b1018,b337,b522,b639,b938,b76],[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b171,b443,b341,b551,b996,b337,b522,b639,b938,b76],[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b171,b443,b341,b551,b160,b600,b525,b1018,b337,b522,b639,b938,b76]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([2],[1]) = [[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[(lowerHistoryComplement lowerHistoryH7)],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,2,1,2],[3,1,3,1]),(false,true)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([2],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have hf3 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1313, h0, h1, h16, h17, h18, h19, h35, h36, h56, h57, h60, h58, h72, h73, h74, h78, h79, h80, h81, h82, h83, h84, h85, h86, h87, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1313 : lowerHistorySourcePremises path1313 = raw1313.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1313 RootOps19.actualOps bv25 bv46 bv76 bv132 bv160 bv171 bv261 bv337 bv341 bv371 bv433 bv443 bv449 bv451 bv522 bv525 bv551 bv600 bv639 bv799 bv839 bv843 bv938 bv996 bv1009 bv1018 bv1162 op0 op1 op16 op17 op18 op19 op35 op36 op56 op57 op60 op58 op72 op73 op74 op78 op79 op80 op81 op82 op83 op84 op85 op86 op87
theorem dedup1313 : raw1313.map List.eraseDups = expected1313 := by
  decide +kernel
theorem source1313 : lowerHistorySourcePremises path1313 = expected1313 := (rawSource1313).trans (dedup1313)
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def src1313 : List (List Nat) := [[371,843,433,1162,839,132,799,261,451,25,449,46,1009,341,551,996,337,522,639,938,76],[371,843,433,1162,839,132,799,261,451,25,449,46,1009,341,551,160,600,525,1018,337,522,639,938,76],[371,843,433,1162,839,132,799,261,451,25,449,46,171,443,341,551,996,337,522,639,938,76],[371,843,433,1162,839,132,799,261,451,25,449,46,171,443,341,551,160,600,525,1018,337,522,639,938,76]]
theorem sourceIDs1313 : lowerHistorySourcePremises path1313 = src1313.map (List.map lowerHistoryBound) := by
  have hb : src1313.map (List.map lowerHistoryBound) = expected1313 := by
    simp only [src1313, expected1313, List.map_cons, List.map_nil, bound25, bound46, bound76, bound132, bound160, bound171, bound261, bound337, bound341, bound371, bound433, bound443, bound449, bound451, bound522, bound525, bound551, bound600, bound639, bound799, bound839, bound843, bound938, bound996, bound1009, bound1018, bound1162]
  exact source1313.trans hb.symm
theorem length1313 : path1313.alternatives = (lowerHistorySourcePremises path1313).length := by
  rw [sourceIDs1313]
  rfl
theorem binding1313 : lowerHistoryPathBinding path1313 := by
  apply BindingIds19.pathBinding_from_ids path1313 src1313 [] recs1313 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1313 rfl records1313 rfl
  · intro r hr _
    simp only [recs1313, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise750)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise746)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise748)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise744)
  · intro r hr _
    simp only [recs1313, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [blockWids, path1313] using witness459_projection
    · simpa only [blockWids, path1313] using witness459_projection
    · simpa only [blockWids, path1313] using witness459_projection
    · simpa only [blockWids, path1313] using witness459_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1313 recs1313 records1313 length1313 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
open BindingNumeric20
theorem op88 : lowerHistoryNormalization ([1,2,1,1],[1]) true false = bv79 := by
  norm_num [bv79, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op89 : lowerHistoryNecessary ⟨⟨([3,1,2,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,2,1,1],[1]) = some [bv633] := by
  decide +kernel
theorem op90 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([1,2,1,1],[1]) true = bv190 := by
  norm_num [bv190, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op91 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([1,2,1,1],[1]) true = bv660 := by
  norm_num [bv660, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op92 : lowerHistoryPull (lowerHistoryHN) ([1,2,1,1],[1]) true = bv79 := by
  norm_num [bv79, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op93 : lowerHistoryPull (lowerHistoryH2) ([1,2,1,1],[1]) true = bv1036 := by
  norm_num [bv1036, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op94 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH2)) ([1,2,1,1],[1]) true = bv190 := by
  norm_num [bv190, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op95 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH5)) ([1,2,1,1],[1]) true = bv660 := by
  norm_num [bv660, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op96 : lowerHistoryPull ((lowerHistoryComplement lowerHistoryH21)) ([1,2,1,1],[1]) true = bv577 := by
  norm_num [bv577, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op97 : lowerHistoryPull (lowerHistoryH23) ([1,2,1,1],[1]) true = bv1058 := by
  norm_num [bv1058, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op98 : lowerHistoryNormalization ([1,2,1,1,1],[1]) true true = bv346 := by
  norm_num [bv346, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op99 : lowerHistoryNecessary ⟨⟨([3,1,2,1,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,2,1,1,1],[1]) = some [bv557] := by
  decide +kernel
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def path1314 : LowerHistoryPath := ⟨.initial,228,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,2,1,1],[3,1,3,1]),(false,true),true,3,⟨(1/4),(1/3),(5/19),(4/15)⟩,1⟩
noncomputable def raw1314 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv79,bv633,bv190,bv660,bv79]]
noncomputable def expected1314 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv79,bv633,bv190,bv660]]
theorem structural1314 (ops : RootOps19.SourceOps) (b25 b46 b79 b132 b190 b261 b371 b433 b449 b451 b633 b660 b799 b839 b843 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h16 : ops.normalization ([1],[]) false false = b839)
    (h17 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h18 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = b799)
    (h19 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = b261)
    (h35 : ops.normalization ([1,2],[1]) false false = b451)
    (h36 : ops.necessary ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1,2],[1]) = some [b25])
    (h56 : ops.normalization ([1,2,1],[1]) false false = b449)
    (h57 : ops.necessary ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,2,1],[1]) = some [b46])
    (h88 : ops.normalization ([1,2,1,1],[1]) true false = b79)
    (h89 : ops.necessary ⟨⟨([3,1,2,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,2,1,1],[1]) = some [b633])
    (h90 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([1,2,1,1],[1]) true = b190)
    (h91 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([1,2,1,1],[1]) true = b660)
    (h92 : ops.pull (lowerHistoryHN) ([1,2,1,1],[1]) true = b79)
    : RootOps19.eval ops path1314 = ([[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b79,b633,b190,b660,b79]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([2],[1]) = [[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1314, h0, h1, h16, h17, h18, h19, h35, h36, h56, h57, h88, h89, h90, h91, h92, hc0, hc1, hc2, hf0, hf1, hf2, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1314 : lowerHistorySourcePremises path1314 = raw1314.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1314 RootOps19.actualOps bv25 bv46 bv79 bv132 bv190 bv261 bv371 bv433 bv449 bv451 bv633 bv660 bv799 bv839 bv843 bv1162 op0 op1 op16 op17 op18 op19 op35 op36 op56 op57 op88 op89 op90 op91 op92
theorem dedup1314 : raw1314.map List.eraseDups = expected1314 := by
  decide +kernel
theorem source1314 : lowerHistorySourcePremises path1314 = expected1314 := (rawSource1314).trans (dedup1314)
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def src1314 : List (List Nat) := [[371,843,433,1162,839,132,799,261,451,25,449,46,79,633,190,660]]
theorem sourceIDs1314 : lowerHistorySourcePremises path1314 = src1314.map (List.map lowerHistoryBound) := by
  have hb : src1314.map (List.map lowerHistoryBound) = expected1314 := by
    simp only [src1314, expected1314, List.map_cons, List.map_nil, bound25, bound46, bound79, bound132, bound190, bound261, bound371, bound433, bound449, bound451, bound633, bound660, bound799, bound839, bound843, bound1162]
  exact source1314.trans hb.symm
theorem length1314 : path1314.alternatives = (lowerHistorySourcePremises path1314).length := by
  rw [sourceIDs1314]
  rfl
theorem binding1314 : lowerHistoryPathBinding path1314 := by
  apply BindingIds19.pathBinding_from_ids path1314 src1314 [] recs1314 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1314 rfl records1314 rfl
  · intro r hr _
    simp only [recs1314, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise756)
  · intro r hr _
    simp only [recs1314, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [blockWids, path1314] using witness391_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1314 recs1314 records1314 length1314 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
open BindingNumeric20
theorem op100 : lowerHistoryPull (lowerHistoryH7) ([1,2,1,1,1],[1]) true = bv688 := by
  norm_num [bv688, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op101 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([1,2,1,1,1],[1]) true = bv962 := by
  norm_num [bv962, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
theorem op102 : lowerHistoryPull (lowerHistoryHN) ([1,2,1,1,1],[1]) true = bv87 := by
  norm_num [bv87, lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def path1315 : LowerHistoryPath := ⟨.initial,229,[3],([1],[]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,1,1],[3,1,3,1]),(true,true),true,1,⟨(1/4),(1/3),(5/19),(4/15)⟩,2⟩
noncomputable def raw1315 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv79,bv633,bv1036,bv346,bv557,bv688,bv962,bv87],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv79,bv633,bv190,bv660,bv577,bv1058,bv346,bv557,bv688,bv962,bv87]]
noncomputable def expected1315 : List (List CertBound) := [[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv79,bv633,bv1036,bv346,bv557,bv688,bv962,bv87],[bv371,bv843,bv433,bv1162,bv839,bv132,bv799,bv261,bv451,bv25,bv449,bv46,bv79,bv633,bv190,bv660,bv577,bv1058,bv346,bv557,bv688,bv962,bv87]]
theorem structural1315 (ops : RootOps19.SourceOps) (b25 b46 b79 b87 b132 b190 b261 b346 b371 b433 b449 b451 b557 b577 b633 b660 b688 b799 b839 b843 b962 b1036 b1058 b1162 : CertBound)
    (h0 : [lowerHistoryZero,lowerHistoryHN,lowerHistoryConstantBound (729/1024) true true,lowerHistoryConstantBound (225/289) false true] = [b371,b843,b433,b1162])
    (h1 : ([] : List CertBound) = [])
    (h16 : ops.normalization ([1],[]) false false = b839)
    (h17 : ops.necessary ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([1],[]) = some [b132])
    (h18 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1],[]) false = b799)
    (h19 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1],[]) false = b261)
    (h35 : ops.normalization ([1,2],[1]) false false = b451)
    (h36 : ops.necessary ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1,2],[1]) = some [b25])
    (h56 : ops.normalization ([1,2,1],[1]) false false = b449)
    (h57 : ops.necessary ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1,2,1],[1]) = some [b46])
    (h88 : ops.normalization ([1,2,1,1],[1]) true false = b79)
    (h89 : ops.necessary ⟨⟨([3,1,2,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([1,2,1,1],[1]) = some [b633])
    (h93 : ops.pull (lowerHistoryH2) ([1,2,1,1],[1]) true = b1036)
    (h94 : ops.pull ((lowerHistoryComplement lowerHistoryH2)) ([1,2,1,1],[1]) true = b190)
    (h95 : ops.pull ((lowerHistoryComplement lowerHistoryH5)) ([1,2,1,1],[1]) true = b660)
    (h96 : ops.pull ((lowerHistoryComplement lowerHistoryH21)) ([1,2,1,1],[1]) true = b577)
    (h97 : ops.pull (lowerHistoryH23) ([1,2,1,1],[1]) true = b1058)
    (h98 : ops.normalization ([1,2,1,1,1],[1]) true true = b346)
    (h99 : ops.necessary ⟨⟨([3,1,2,1,1,1],[3,1,3,1]),(true,true)⟩,true,true,some (true,([],[1]),false)⟩ ([1,2,1,1,1],[1]) = some [b557])
    (h100 : ops.pull (lowerHistoryH7) ([1,2,1,1,1],[1]) true = b688)
    (h101 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([1,2,1,1,1],[1]) true = b962)
    (h102 : ops.pull (lowerHistoryHN) ([1,2,1,1,1],[1]) true = b87)
    : RootOps19.eval ops path1315 = ([[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b79,b633,b1036,b346,b557,b688,b962,b87],[b371,b843,b433,b1162,b839,b132,b799,b261,b451,b25,b449,b46,b79,b633,b190,b660,b577,b1058,b346,b557,b688,b962,b87]] : List (List CertBound)).map List.eraseDups := by
  have hc0 : lowerHistorySourceChoices ⟨⟨([3,1],[3,1,3]),(true,false)⟩,false,false,none⟩ ([2],[1]) = [[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5)]] := by rfl
  have hc1 : lowerHistorySourceChoices ⟨⟨([3,1,2],[3,1,3,1]),(false,true)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc2 : lowerHistorySourceChoices ⟨⟨([3,1,2,1],[3,1,3,1]),(true,true)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hc3 : lowerHistorySourceChoices ⟨⟨([3,1,2,1,1],[3,1,3,1]),(false,true)⟩,true,true,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[(lowerHistoryComplement lowerHistoryH2),(lowerHistoryComplement lowerHistoryH5),(lowerHistoryComplement lowerHistoryH21),lowerHistoryH23]] := by rfl
  have hf0 : decide ((([2],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf1 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf2 : decide ((([1],[]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by decide
  have hf3 : decide ((([],[1]) : LowerLabel) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by decide
  have he0 : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have he1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have he2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  simp only [RootOps19.eval, path1315, h0, h1, h16, h17, h18, h19, h35, h36, h56, h57, h88, h89, h93, h94, h95, h96, h97, h98, h99, h100, h101, h102, hc0, hc1, hc2, hc3, hf0, hf1, hf2, hf3, he0, he1, he2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
theorem rawSource1315 : lowerHistorySourcePremises path1315 = raw1315.map List.eraseDups := by
  rw [← RootOps19.actual_eval]
  exact structural1315 RootOps19.actualOps bv25 bv46 bv79 bv87 bv132 bv190 bv261 bv346 bv371 bv433 bv449 bv451 bv557 bv577 bv633 bv660 bv688 bv799 bv839 bv843 bv962 bv1036 bv1058 bv1162 op0 op1 op16 op17 op18 op19 op35 op36 op56 op57 op88 op89 op93 op94 op95 op96 op97 op98 op99 op100 op101 op102
theorem dedup1315 : raw1315.map List.eraseDups = expected1315 := by
  decide +kernel
theorem source1315 : lowerHistorySourcePremises path1315 = expected1315 := (rawSource1315).trans (dedup1315)
end M7ContinueSep17.Initial20260918.B1310_1315

set_option Elab.async false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
open Freiman M7SplitSep17
namespace M7ContinueSep17.Initial20260918.B1310_1315
noncomputable def src1315 : List (List Nat) := [[371,843,433,1162,839,132,799,261,451,25,449,46,79,633,1036,346,557,688,962,87],[371,843,433,1162,839,132,799,261,451,25,449,46,79,633,190,660,577,1058,346,557,688,962,87]]
theorem sourceIDs1315 : lowerHistorySourcePremises path1315 = src1315.map (List.map lowerHistoryBound) := by
  have hb : src1315.map (List.map lowerHistoryBound) = expected1315 := by
    simp only [src1315, expected1315, List.map_cons, List.map_nil, bound25, bound46, bound79, bound87, bound132, bound190, bound261, bound346, bound371, bound433, bound449, bound451, bound557, bound577, bound633, bound660, bound688, bound799, bound839, bound843, bound962, bound1036, bound1058, bound1162]
  exact source1315.trans hb.symm
theorem length1315 : path1315.alternatives = (lowerHistorySourcePremises path1315).length := by
  rw [sourceIDs1315]
  rfl
theorem binding1315 : lowerHistoryPathBinding path1315 := by
  apply BindingIds19.pathBinding_from_ids path1315 src1315 [] recs1315 blockWids blockPreIDs 1025 1194
    ⟨premise_size, witness_size⟩ sourceIDs1315 rfl records1315 rfl
  · intro r hr _
    simp only [recs1315, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise754)
    · simpa only [blockPreIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise752)
  · intro r hr _
    simp only [recs1315, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [blockWids, path1315] using witness477_projection
    · simpa only [blockWids, path1315] using witness477_projection
  · decide +kernel
  · exact BatchCoverage15.coverage_sound path1315 recs1315 records1315 length1315 (by decide +kernel)
end M7ContinueSep17.Initial20260918.B1310_1315

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
namespace M7ContinueSep17.Initial20260918.B1310_1315
theorem _root_.solution : lowerHistoryBindingBatch 1310 1315 := by
  intro i hlo hhi p hp
  interval_cases i
  · have hl : lowerHistoryPaths[1310]? = some M7ContinueSep17.Initial20260918.B1310_1315.path1311 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 224 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1311
  · have hl : lowerHistoryPaths[1311]? = some M7ContinueSep17.Initial20260918.B1310_1315.path1312 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 225 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1312
  · have hl : lowerHistoryPaths[1312]? = some M7ContinueSep17.Initial20260918.B1310_1315.path1313 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 226 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1313
  · have hl : lowerHistoryPaths[1313]? = some M7ContinueSep17.Initial20260918.B1310_1315.path1314 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 227 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1314
  · have hl : lowerHistoryPaths[1314]? = some M7ContinueSep17.Initial20260918.B1310_1315.path1315 := by
      rw [M7ContinueSep17.CatalogueGeneral.pathLookupH 228 (by decide)]
      rfl
    have he := Option.some.inj (hl.symm.trans hp)
    subst p
    exact binding1315
end M7ContinueSep17.Initial20260918.B1310_1315

#print axioms solution
