-- Prove2me | solution 1 for Freiman.lowerHistory_source_path129_sep15
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T15:58:18.362018+00:00
-- url     : https://prove2.me/submissions/970564b7-3d24-424f-8171-745d828a3cfd

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
namespace M7Binding100Sep15
set_option Elab.async false
set_option linter.all false
attribute [local irreducible] Freiman.lowerHistoryBound




open Freiman
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option linter.all false
namespace RootInv18
private theorem quadratic_three (a b : ℚ) :
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

private theorem quadratic_twenty_one (a d : ℚ) :
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

open Freiman
namespace RootPull18
private theorem complement (b : CertBound) (words : LowerPair) (orientation : Bool) :
    lowerHistoryPull (lowerHistoryComplement b) words orientation =
      lowerHistoryComplement (lowerHistoryPull b words orientation) := by
  cases orientation <;> rfl
end RootPull18

open Freiman
open Freiman
namespace RootOps19
private structure SourceOps where
  relaxed : LowerHistoryContext → Option (List CertBound)
  necessary : LowerHistoryState → LowerPair → Option (List CertBound)
  normalization : LowerPair → Bool → Bool → CertBound
  pull : CertBound → LowerPair → Bool → CertBound

private def actualOps : SourceOps :=
  ⟨lowerHistoryRelaxedGoodness, lowerHistoryNecessary, lowerHistoryNormalization, lowerHistoryPull⟩

private def eval (ops : SourceOps) (p : LowerHistoryPath) : List (List CertBound) := Id.run do
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

private theorem actual_eval (p : LowerHistoryPath) : eval actualOps p = lowerHistorySourcePremises p := by
  rfl

end RootOps19

open Freiman
namespace BindingNumeric17
set_option Elab.async true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def h2 : CertBound := ⟨true,true,⟨⟨37/50,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩,⟨125/214,-1/214,0,0⟩,⟨52/73,1/73,0,0⟩⟩⟩
private def h5 : CertBound := ⟨false,true,⟨⟨279/500,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨66/179,-1/537,0,0⟩,⟨4/13,1/13,0,0⟩,⟨125/214,-1/214,0,0⟩⟩⟩
private def h6 : CertBound := ⟨false,true,⟨⟨69/200,0,0,0⟩,⟨39/134,0,0,1/402⟩,⟨15/34,0,0,-1/34⟩,⟨1/10,0,0,1/10⟩,⟨119/202,0,0,-1/202⟩⟩⟩
private def h7 : CertBound := ⟨true,false,⟨⟨31/100,0,0,0⟩,⟨5/22,1/22,0,0⟩,⟨2,-1,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
private def h7m : CertBound := ⟨false,true,⟨⟨161/500,0,0,0⟩,⟨5/22,1/22,0,0⟩,⟨2,-1,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
private def h9 : CertBound := ⟨false,false,⟨⟨3/2,-1/2,0,0⟩,⟨-1/2,1/2,0,0⟩,⟨4/13,1/13,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
private def h21 : CertBound := ⟨false,true,⟨⟨-2334/781,1646/781,0,0⟩,⟨4/13,1/13,0,0⟩,⟨2,-1,0,0⟩,⟨42/143,1/429,0,0⟩,⟨9/13,-1/13,0,0⟩⟩⟩
private def h23 : CertBound := ⟨true,true,⟨⟨139/250,0,0,0⟩,⟨4/13,1/13,0,0⟩,⟨9/13,-1/13,0,0⟩,⟨1/2,1/6,0,0⟩,⟨125/214,-1/214,0,0⟩⟩⟩
private def hn : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨-3/2,0,0,1/2⟩,⟨-1/2,0,0,1/6⟩,⟨-3/2,0,0,1/2⟩,⟨-1/2,0,0,1/6⟩⟩⟩
private theorem bases : lowerHistoryH2=h2 ∧ lowerHistoryH5=h5 ∧ lowerHistoryH6=h6 ∧ lowerHistoryH7=h7 ∧ lowerHistoryH7Mixed=h7m ∧ lowerHistoryH9=h9 ∧ lowerHistoryH21=h21 ∧ lowerHistoryH23=h23 ∧ lowerHistoryHN=hn := by
  norm_num [h2,h5,h6,h7,h7m,h9,h21,h23,hn,lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7,lowerHistoryH7Mixed,lowerHistoryH9,lowerHistoryH21,lowerHistoryH23,lowerHistoryHN,lowerHistoryPB,lowerHistoryTheta,lowerHistoryConstantBound,lowerHistoryThreshold,lowerHistorySort,lowerHistoryLex,lowerHistoryWH,lowerHistoryCF,lowerHistoryMatrix,lowerHistoryDiv,RootInv18.quadratic_three,RootInv18.quadratic_twenty_one,lowerHistoryAbs,lowerHistorySign,lowerHistoryQuadSign,lowerHistoryRatSign,lowerHistoryNeg,lowerHistoryAlpha,lowerHistoryBeta,lowerHistoryTau,lowerHistoryRat,certFieldScale,certFieldMul,certFieldAdd,certFieldSub]
private theorem bh2 : lowerHistoryH2=h2 := bases.1
private theorem bh5 : lowerHistoryH5=h5 := bases.2.1
private theorem bh6 : lowerHistoryH6=h6 := bases.2.2.1
private theorem bh7 : lowerHistoryH7=h7 := bases.2.2.2.1
private theorem bh7m : lowerHistoryH7Mixed=h7m := bases.2.2.2.2.1
private theorem bh9 : lowerHistoryH9=h9 := bases.2.2.2.2.2.1
private theorem bh21 : lowerHistoryH21=h21 := bases.2.2.2.2.2.2.1
private theorem bh23 : lowerHistoryH23=h23 := bases.2.2.2.2.2.2.2.1
private theorem bhn : lowerHistoryHN=hn := bases.2.2.2.2.2.2.2.2
private theorem initial_base : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
    [⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩,⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩,⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩,⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩] := by
  rw [bhn, bh7, bh9]
  rfl
private theorem norm0 : lowerHistoryNormalization ([2],[3]) false false = ⟨false,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm19 : lowerHistoryNormalization ([2,2,1],[3,1]) false false = ⟨false,false,⟨⟨(1167/4454),0,0,(71/4454)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm33 : lowerHistoryNormalization ([2,2],[3]) true true = ⟨true,true,⟨⟨(387/1394),0,0,(19/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm34 : lowerHistoryNormalization ([2,2,1],[3]) true true = ⟨true,true,⟨⟨(339/2227),0,0,(-8/2227)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm35 : lowerHistoryNormalization ([2,2,1,1],[3,1]) false false = ⟨false,false,⟨⟨(887/11135),0,0,(112/11135)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(73/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm38 : lowerHistoryNormalization ([2,2,1,1,2],[3,1]) true true = ⟨true,true,⟨⟨(9139/635134),0,0,(1065/635134)⟩,⟨(487/1174),0,0,(1/1174)⟩,⟨(455/1082),0,0,(-1/3246)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm39 : lowerHistoryNormalization ([2,2,1,1,2,1],[3,1]) true true = ⟨true,true,⟨⟨(6009/844106),0,0,(2215/5908742)⟩,⟨(487/1174),0,0,(1/1174)⟩,⟨(603/1438),0,0,(-1/10066)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey0 : lowerHistoryPull (lowerHistoryH7) ([2],[3]) false = ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey1 : lowerHistoryPull (lowerHistoryH9) ([2],[3]) false = ⟨false,false,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey84 : lowerHistoryPull (lowerHistoryH2) ([2,2],[3]) true = ⟨false,true,⟨⟨(462273050/1111577051),(-149450/1111577051),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey85 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,2],[3]) true = ⟨false,false,⟨⟨(47955895000/83153712699),(-16982000/9239301411),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey86 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,2],[3]) true = ⟨false,false,⟨⟨(2901217/14169794),(2384679/14169794),0,0⟩,⟨(5498/13393),(1/13393),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey87 : lowerHistoryPull (lowerHistoryH23) ([2,2],[3]) true = ⟨false,true,⟨⟨(19056750/31877287),(-984250/31877287),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey88 : lowerHistoryPull (lowerHistoryH7) ([2,2,1,1],[3,1]) false = ⟨true,false,⟨⟨(299259802/9067496425),(154281327/18134992850),0,0⟩,⟨(1696/4057),(1/4057),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey93 : lowerHistoryPull (lowerHistoryH9) ([2,2,1,1],[3,1]) false = ⟨false,false,⟨⟨(2677899/2393339),(-1425589/2393339),0,0⟩,⟨(28/71),(1/71),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey94 : lowerHistoryPull (lowerHistoryH2) ([2,2,1,1,2],[3,1]) true = ⟨false,true,⟨⟨(7253355050/271146465733),(1681961850/10032419232121),0,0⟩,⟨(47811/114169),(-1/114169),0,0⟩,⟨(129497/309166),(1/309166),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey95 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,2,1,1,2],[3,1]) true = ⟨false,false,⟨⟨(316256997500/9271755553203),(6554204000/9271755553203),0,0⟩,⟨(129497/309166),(1/309166),0,0⟩,⟨(6543/15613),(-1/15613),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey96 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,2,1,1,2],[3,1]) true = ⟨false,false,⟨⟨(152368767/13671894764),(437763265/41015684292),0,0⟩,⟨(8398/20053),(1/20053),0,0⟩,⟨(71431/170447),(-1/511341),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey97 : lowerHistoryPull (lowerHistoryH23) ([2,2,1,1,2],[3,1]) true = ⟨false,true,⟨⟨(8212062250/214247245927),(-358907750/214247245927),0,0⟩,⟨(129497/309166),(1/309166),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey98 : lowerHistoryPull (lowerHistoryH7) ([2,2,1,1,2,1],[3,1]) true = ⟨false,false,⟨⟨(1307275450/29736883517),(-12001600/959254307),0,0⟩,⟨(14933/35662),(1/35662),0,0⟩,⟨(22533/53797),(-1/53797),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey99 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,2,1,1,2,1],[3,1]) true = ⟨false,true,⟨⟨(11955219/1918508614),(20894693/5755525842),0,0⟩,⟨(14933/35662),(1/35662),0,0⟩,⟨(22533/53797),(-1/53797),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey100 : lowerHistoryPull (lowerHistoryHN) ([2,2,1,1,2,1],[3,1]) true = ⟨true,false,⟨⟨(6009/844106),0,0,(2215/5908742)⟩,⟨(487/1174),0,0,(1/1174)⟩,⟨(603/1438),0,0,(-1/10066)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pull66 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH7) ([2],[3]) false = ⟨false,true,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey0]
  rfl
private theorem pull96 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,2],[3]) true = ⟨true,false,⟨⟨(462273050/1111577051),(-149450/1111577051),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey84]
  rfl
private theorem pull100 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH7) ([2,2,1,1],[3,1]) false = ⟨false,true,⟨⟨(299259802/9067496425),(154281327/18134992850),0,0⟩,⟨(1696/4057),(1/4057),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey88]
  rfl
private theorem pull108 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,2,1,1,2],[3,1]) true = ⟨true,false,⟨⟨(7253355050/271146465733),(1681961850/10032419232121),0,0⟩,⟨(47811/114169),(-1/114169),0,0⟩,⟨(129497/309166),(1/309166),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey94]
  rfl
end BindingNumeric17
set_option Elab.async false

open Freiman
namespace BindingSourceBranches17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem branchesG0 :
    (lowerHistoryNecessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [⟨true,false,⟨⟨(-2415463/5270749),(1816717/5270749),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,3,3],[3,1]) = some [⟨false,false,⟨⟨(15846/447863),(105176/1343589),0,0⟩,⟨(529/1222),(1/1222),0,0⟩,⟨(8265/19058),(-1/57174),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,3,1],[3,1]) = some [⟨false,false,⟨⟨(2496968/95947501),(5603863/287842503),0,0⟩,⟨(8265/19058),(-1/57174),0,0⟩,⟨(4367/10069),(1/10069),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,3,2],[3,1]) = some [⟨false,false,⟨⟨(482605/7364591),(3580367/22093773),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,2,1],[3,1]) = some [⟨false,false,⟨⟨(2664700/82712279),(5005419/82712279),0,0⟩,⟨(2455/5638),(1/5638),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,3,1],[3,1]) = some [⟨false,false,⟨⟨(534009/1863433),(1199347/5590299),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,1,1],[3,1]) = some [⟨false,false,⟨⟨(661229/9815663),(4179215/29446989),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
  decide +kernel
private theorem branchesG4 :
    (lowerHistoryNecessary ⟨⟨([2,2,3,1,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,1,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(553621/54005783),(1114296/54005783),0,0⟩,⟨(7406/16861),(1/16861),0,0⟩,⟨(2815/6406),(-1/6406),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,3,1],[3,1]) = some [⟨false,false,⟨⟨(534009/1863433),(1199347/5590299),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,3],[3,1]) = some [⟨true,false,⟨⟨(-2415463/5270749),(1816717/5270749),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3],[3,1,3,1]),(false,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,3],[3,1]) = some [⟨false,false,⟨⟨(911720/2447159),(6369548/7341477),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,2],[3]) = some [⟨false,false,⟨⟨(8171/31993),(22664/31993),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,2,1],[3]) = some [⟨false,false,⟨⟨(100728/735839),(193103/735839),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [⟨true,false,⟨⟨(-1707521/5116787),(1276674/5116787),0,0⟩,⟨(594/1417),(1/1417),0,0⟩,⟨(133/314),(-1/942),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,2,1,1],[3,1]) = some [⟨true,false,⟨⟨(-4541489/36558707),(3402426/36558707),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(515/1226),(-1/3678),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩]) := by
  decide +kernel
private theorem branchesG5 :
    (lowerHistoryNecessary ⟨⟨([2,2,2,1,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,2,1,1,3],[3,1]) = some [⟨false,false,⟨⟨(100002328/10230119029),(237472556/10230119029),0,0⟩,⟨(1696/4057),(1/4057),0,0⟩,⟨(81134/193969),(-1/193969),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2,1,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,1,1,3,1],[3,1]) = some [⟨false,false,⟨⟨(659389499/86210879833),(493780203/86210879833),0,0⟩,⟨(81134/193969),(-1/193969),0,0⟩,⟨(14301/34189),(1/34189),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,2,1,1,2],[3,1]) = some [⟨false,false,⟨⟨(774590/45743113),(6280201/137229339),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2,1,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,1,1,2,1],[3,1]) = some [⟨false,false,⟨⟨(3244125/353754973),(17963014/1061264919),0,0⟩,⟨(8398/20053),(1/20053),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2,1,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,2,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(41390/868621),(245197/2605863),0,0⟩,⟨(594/1417),(1/1417),0,0⟩,⟨(515/1226),(-1/3678),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2,1,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,1,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(1380237/76988509),(8310670/230965527),0,0⟩,⟨(4055/9661),(1/9661),0,0⟩,⟨(515/1226),(-1/3678),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,2,1],[3,1]) = some [⟨false,false,⟨⟨(254992/735839),(472767/735839),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,2],[3,1]) = some [⟨true,false,⟨⟨(-4078497/4976303),(3063403/4976303),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩]) := by
  decide +kernel
end BindingSourceBranches17

open Freiman
namespace BindingSourceSupport17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem relaxed2 : lowerHistoryRelaxedGoodness ⟨([2],[3,1]),(false,false)⟩ = some [⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩] := by
  decide +kernel
private def fingerprint (b : CertBound) : Bool × Bool × Int × Nat :=
  (b.lower, b.strict, b.threshold.c.a.num, b.threshold.c.a.den)
private theorem erase_self_of_nodup {l : List CertBound} (h : l.Nodup) : l.eraseDups = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hf : l.filter (fun b => !(b == a)) = l := by
      apply List.filter_eq_self.mpr
      intro b hb
      simp only [Bool.not_eq_true']
      exact beq_eq_false_iff_ne.mpr (fun e => (List.nodup_cons.mp h).1 (e ▸ hb))
    rw [List.eraseDups_cons, hf, ih h.tail]
end BindingSourceSupport17

open Freiman
open RootOps19
set_option linter.all false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace BindingOps17_129
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b8 : CertBound) (b21 : CertBound) (b34 : CertBound) (b136 : CertBound) (b180 : CertBound) (b191 : CertBound) (b260 : CertBound) (b267 : CertBound) (b275 : CertBound) (b371 : CertBound) (b376 : CertBound) (b385 : CertBound) (b416 : CertBound) (b420 : CertBound) (b440 : CertBound) (b545 : CertBound) (b560 : CertBound) (b591 : CertBound) (b649 : CertBound) (b663 : CertBound) (b711 : CertBound) (b746 : CertBound) (b772 : CertBound) (b780 : CertBound) (b781 : CertBound) (b821 : CertBound) (b843 : CertBound) (b845 : CertBound) (b856 : CertBound) (b876 : CertBound) (b957 : CertBound) (b1025 : CertBound) (b1037 : CertBound) (b1046 : CertBound) (b1146 : CertBound) (b1153 : CertBound) (b1157 : CertBound)
private def path : LowerHistoryPath := ⟨.left,129,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,16⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([2,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,2],[3]) = some [b780])
    (hb2 : ops.necessary ⟨⟨([2,2,2,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,2,1],[3]) = some [b746])
    (hb3 : ops.necessary ⟨⟨([2,2,2,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [b8])
    (hb4 : ops.necessary ⟨⟨([2,2,2,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,2,1,1],[3,1]) = some [b34])
    (hb5 : ops.necessary ⟨⟨([2,2,2,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,2,1,1,2],[3,1]) = some [b591])
    (hb6 : ops.necessary ⟨⟨([2,2,2,1,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,1,1,2,1],[3,1]) = some [b545])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2],[3]) false = b1153)
    (hn2 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn3 : ops.pull (lowerHistoryH9) ([2],[3]) false = b876)
    (hn4 : ops.normalization ([2,2],[3]) true true = b420)
    (hn5 : ops.pull (lowerHistoryH2) ([2,2],[3]) true = b1146)
    (hn6 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,2],[3]) true = b267)
    (hn7 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,2],[3]) true = b821)
    (hn8 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,2],[3]) true = b772)
    (hn9 : ops.pull (lowerHistoryH23) ([2,2],[3]) true = b1157)
    (hn10 : ops.normalization ([2,2,1],[3]) true true = b416)
    (hn11 : ops.normalization ([2,2,1],[3,1]) false false = b781)
    (hn12 : ops.normalization ([2,2,1,1],[3,1]) false false = b711)
    (hn13 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,2,1,1],[3,1]) false = b1037)
    (hn14 : ops.pull (lowerHistoryH7) ([2,2,1,1],[3,1]) false = b191)
    (hn15 : ops.pull (lowerHistoryH9) ([2,2,1,1],[3,1]) false = b845)
    (hn16 : ops.normalization ([2,2,1,1,2],[3,1]) true true = b385)
    (hn17 : ops.pull (lowerHistoryH2) ([2,2,1,1,2],[3,1]) true = b1025)
    (hn18 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,2,1,1,2],[3,1]) true = b180)
    (hn19 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,2,1,1,2],[3,1]) true = b649)
    (hn20 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,2,1,1,2],[3,1]) true = b560)
    (hn21 : ops.pull (lowerHistoryH23) ([2,2,1,1,2],[3,1]) true = b1046)
    (hn22 : ops.normalization ([2,2,1,1,2,1],[3,1]) true true = b376)
    (hn23 : ops.pull (lowerHistoryH7) ([2,2,1,1,2,1],[3,1]) true = b663)
    (hn24 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,2,1,1,2,1],[3,1]) true = b957)
    (hn25 : ops.pull (lowerHistoryHN) ([2,2,1,1,2,1],[3,1]) true = b136)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[1])
    (herase2 : [b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[2])
    (herase3 : [b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[3])
    (herase4 : [b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[4])
    (herase5 : [b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[5])
    (herase6 : [b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[6])
    (herase7 : [b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[7])
    (herase8 : [b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[8])
    (herase9 : [b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[9])
    (herase10 : [b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[10])
    (herase11 : [b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[11])
    (herase12 : [b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[12])
    (herase13 : [b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[13])
    (herase14 : [b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[14])
    (herase15 : [b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound))[15])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b1153,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b1146,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b1037,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b1025,b376,b545,b663,b957,b136],
[b371,b843,b260,b440,b3,b856,b21,b275,b876,b420,b780,b267,b821,b772,b1157,b416,b746,b781,b8,b711,b34,b191,b845,b385,b591,b180,b649,b560,b1046,b376,b545,b663,b957,b136]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([2,2,2],[3,1,3]),(false,true)⟩,true,false,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([2,2,2,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([2,2,2,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice4 : lowerHistorySourceChoices ⟨⟨([2,2,2,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hdone4 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced4 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice5 : lowerHistorySourceChoices ⟨⟨([2,2,2,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone5 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced5 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20, hn21, hn22, hn23, hn24, hn25, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, hchoice4, hdone4, hforced4, hchoice5, hdone5, hforced5, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1, herase2, herase3, herase4, herase5, herase6, herase7, herase8, herase9, herase10, herase11, herase12, herase13, herase14, herase15]
  rfl
end BindingOps17_129

open Freiman

private abbrev sourceBound3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩

private abbrev sourceBound8 : CertBound := ⟨true,false,⟨⟨(-1707521/5116787),(1276674/5116787),0,0⟩,⟨(594/1417),(1/1417),0,0⟩,⟨(133/314),(-1/942),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private abbrev sourceBound21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private abbrev sourceBound34 : CertBound := ⟨true,false,⟨⟨(-4541489/36558707),(3402426/36558707),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(515/1226),(-1/3678),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private abbrev sourceBound136 : CertBound := ⟨true,false,⟨⟨(6009/844106),0,0,(2215/5908742)⟩,⟨(487/1174),0,0,(1/1174)⟩,⟨(603/1438),0,0,(-1/10066)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound180 : CertBound := ⟨true,false,⟨⟨(7253355050/271146465733),(1681961850/10032419232121),0,0⟩,⟨(47811/114169),(-1/114169),0,0⟩,⟨(129497/309166),(1/309166),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound191 : CertBound := ⟨true,false,⟨⟨(299259802/9067496425),(154281327/18134992850),0,0⟩,⟨(1696/4057),(1/4057),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound260 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private abbrev sourceBound267 : CertBound := ⟨true,false,⟨⟨(462273050/1111577051),(-149450/1111577051),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound275 : CertBound := ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound371 : CertBound := ⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

private abbrev sourceBound376 : CertBound := ⟨true,true,⟨⟨(6009/844106),0,0,(2215/5908742)⟩,⟨(487/1174),0,0,(1/1174)⟩,⟨(603/1438),0,0,(-1/10066)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound385 : CertBound := ⟨true,true,⟨⟨(9139/635134),0,0,(1065/635134)⟩,⟨(487/1174),0,0,(1/1174)⟩,⟨(455/1082),0,0,(-1/3246)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound416 : CertBound := ⟨true,true,⟨⟨(339/2227),0,0,(-8/2227)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private abbrev sourceBound420 : CertBound := ⟨true,true,⟨⟨(387/1394),0,0,(19/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private abbrev sourceBound440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private abbrev sourceBound545 : CertBound := ⟨false,false,⟨⟨(3244125/353754973),(17963014/1061264919),0,0⟩,⟨(8398/20053),(1/20053),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound560 : CertBound := ⟨false,false,⟨⟨(152368767/13671894764),(437763265/41015684292),0,0⟩,⟨(8398/20053),(1/20053),0,0⟩,⟨(71431/170447),(-1/511341),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound591 : CertBound := ⟨false,false,⟨⟨(774590/45743113),(6280201/137229339),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound649 : CertBound := ⟨false,false,⟨⟨(316256997500/9271755553203),(6554204000/9271755553203),0,0⟩,⟨(129497/309166),(1/309166),0,0⟩,⟨(6543/15613),(-1/15613),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private abbrev sourceBound663 : CertBound := ⟨false,false,⟨⟨(1307275450/29736883517),(-12001600/959254307),0,0⟩,⟨(14933/35662),(1/35662),0,0⟩,⟨(22533/53797),(-1/53797),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound711 : CertBound := ⟨false,false,⟨⟨(887/11135),0,0,(112/11135)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(73/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound746 : CertBound := ⟨false,false,⟨⟨(100728/735839),(193103/735839),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound772 : CertBound := ⟨false,false,⟨⟨(2901217/14169794),(2384679/14169794),0,0⟩,⟨(5498/13393),(1/13393),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound780 : CertBound := ⟨false,false,⟨⟨(8171/31993),(22664/31993),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound781 : CertBound := ⟨false,false,⟨⟨(1167/4454),0,0,(71/4454)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound821 : CertBound := ⟨false,false,⟨⟨(47955895000/83153712699),(-16982000/9239301411),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound843 : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩

private abbrev sourceBound845 : CertBound := ⟨false,false,⟨⟨(2677899/2393339),(-1425589/2393339),0,0⟩,⟨(28/71),(1/71),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound856 : CertBound := ⟨false,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private abbrev sourceBound876 : CertBound := ⟨false,false,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound957 : CertBound := ⟨false,true,⟨⟨(11955219/1918508614),(20894693/5755525842),0,0⟩,⟨(14933/35662),(1/35662),0,0⟩,⟨(22533/53797),(-1/53797),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1025 : CertBound := ⟨false,true,⟨⟨(7253355050/271146465733),(1681961850/10032419232121),0,0⟩,⟨(47811/114169),(-1/114169),0,0⟩,⟨(129497/309166),(1/309166),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1037 : CertBound := ⟨false,true,⟨⟨(299259802/9067496425),(154281327/18134992850),0,0⟩,⟨(1696/4057),(1/4057),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1046 : CertBound := ⟨false,true,⟨⟨(8212062250/214247245927),(-358907750/214247245927),0,0⟩,⟨(129497/309166),(1/309166),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1146 : CertBound := ⟨false,true,⟨⟨(462273050/1111577051),(-149450/1111577051),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound1153 : CertBound := ⟨false,true,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound1157 : CertBound := ⟨false,true,⟨⟨(19056750/31877287),(-984250/31877287),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman
namespace SourceMemo17_129
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,129,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,16⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport17.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem erase2 : expected[2].eraseDups = expected[2] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[2] (by simp [expected])))
private theorem eraseActual2 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[2] := by
  simpa [expected] using erase2
private theorem erase3 : expected[3].eraseDups = expected[3] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[3] (by simp [expected])))
private theorem eraseActual3 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[3] := by
  simpa [expected] using erase3
private theorem erase4 : expected[4].eraseDups = expected[4] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[4] (by simp [expected])))
private theorem eraseActual4 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[4] := by
  simpa [expected] using erase4
private theorem erase5 : expected[5].eraseDups = expected[5] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[5] (by simp [expected])))
private theorem eraseActual5 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[5] := by
  simpa [expected] using erase5
private theorem erase6 : expected[6].eraseDups = expected[6] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[6] (by simp [expected])))
private theorem eraseActual6 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[6] := by
  simpa [expected] using erase6
private theorem erase7 : expected[7].eraseDups = expected[7] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[7] (by simp [expected])))
private theorem eraseActual7 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound1153,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[7] := by
  simpa [expected] using erase7
private theorem erase8 : expected[8].eraseDups = expected[8] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[8] (by simp [expected])))
private theorem eraseActual8 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[8] := by
  simpa [expected] using erase8
private theorem erase9 : expected[9].eraseDups = expected[9] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[9] (by simp [expected])))
private theorem eraseActual9 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[9] := by
  simpa [expected] using erase9
private theorem erase10 : expected[10].eraseDups = expected[10] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[10] (by simp [expected])))
private theorem eraseActual10 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[10] := by
  simpa [expected] using erase10
private theorem erase11 : expected[11].eraseDups = expected[11] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[11] (by simp [expected])))
private theorem eraseActual11 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound1146,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[11] := by
  simpa [expected] using erase11
private theorem erase12 : expected[12].eraseDups = expected[12] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[12] (by simp [expected])))
private theorem eraseActual12 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[12] := by
  simpa [expected] using erase12
private theorem erase13 : expected[13].eraseDups = expected[13] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[13] (by simp [expected])))
private theorem eraseActual13 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound1037,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[13] := by
  simpa [expected] using erase13
private theorem erase14 : expected[14].eraseDups = expected[14] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[14] (by simp [expected])))
private theorem eraseActual14 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound1025,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[14] := by
  simpa [expected] using erase14
private theorem erase15 : expected[15].eraseDups = expected[15] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[15] (by simp [expected])))
private theorem eraseActual15 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound876,sourceBound420,sourceBound780,sourceBound267,sourceBound821,sourceBound772,sourceBound1157,sourceBound416,sourceBound746,sourceBound781,sourceBound8,sourceBound711,sourceBound34,sourceBound191,sourceBound845,sourceBound385,sourceBound591,sourceBound180,sourceBound649,sourceBound560,sourceBound1046,sourceBound376,sourceBound545,sourceBound663,sourceBound957,sourceBound136].eraseDups = expected[15] := by
  simpa [expected] using erase15
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps17_129.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b8 := sourceBound8) (b21 := sourceBound21) (b34 := sourceBound34) (b136 := sourceBound136) (b180 := sourceBound180) (b191 := sourceBound191) (b260 := sourceBound260) (b267 := sourceBound267) (b275 := sourceBound275) (b371 := sourceBound371) (b376 := sourceBound376) (b385 := sourceBound385) (b416 := sourceBound416) (b420 := sourceBound420) (b440 := sourceBound440) (b545 := sourceBound545) (b560 := sourceBound560) (b591 := sourceBound591) (b649 := sourceBound649) (b663 := sourceBound663) (b711 := sourceBound711) (b746 := sourceBound746) (b772 := sourceBound772) (b780 := sourceBound780) (b781 := sourceBound781) (b821 := sourceBound821) (b843 := sourceBound843) (b845 := sourceBound845) (b856 := sourceBound856) (b876 := sourceBound876) (b957 := sourceBound957) (b1025 := sourceBound1025) (b1037 := sourceBound1037) (b1046 := sourceBound1046) (b1146 := sourceBound1146) (b1153 := sourceBound1153) (b1157 := sourceBound1157)
      BindingSourceSupport17.relaxed2 BindingNumeric17.initial_base (BindingSourceBranches17.branchesG0.1) (BindingSourceBranches17.branchesG4.2.2.2.2.1) (BindingSourceBranches17.branchesG4.2.2.2.2.2.1) (BindingSourceBranches17.branchesG4.2.2.2.2.2.2.1) (BindingSourceBranches17.branchesG4.2.2.2.2.2.2.2) (BindingSourceBranches17.branchesG5.2.2.1) (BindingSourceBranches17.branchesG5.2.2.2.1) BindingNumeric17.norm0 BindingNumeric17.pull66 BindingNumeric17.pullKey0 BindingNumeric17.pullKey1 BindingNumeric17.norm33 BindingNumeric17.pullKey84 BindingNumeric17.pull96 BindingNumeric17.pullKey85 BindingNumeric17.pullKey86 BindingNumeric17.pullKey87 BindingNumeric17.norm34 BindingNumeric17.norm19 BindingNumeric17.norm35 BindingNumeric17.pull100 BindingNumeric17.pullKey88 BindingNumeric17.pullKey93 BindingNumeric17.norm38 BindingNumeric17.pullKey94 BindingNumeric17.pull108 BindingNumeric17.pullKey95 BindingNumeric17.pullKey96 BindingNumeric17.pullKey97 BindingNumeric17.norm39 BindingNumeric17.pullKey98 BindingNumeric17.pullKey99 BindingNumeric17.pullKey100 eraseActual0 eraseActual1 eraseActual2 eraseActual3 eraseActual4 eraseActual5 eraseActual6 eraseActual7 eraseActual8 eraseActual9 eraseActual10 eraseActual11 eraseActual12 eraseActual13 eraseActual14 eraseActual15)
end SourceMemo17_129

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman


private abbrev sourceBound259 : CertBound := ⟨true,false,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private abbrev sourceBound284 : CertBound := ⟨true,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private abbrev sourceBound285 : CertBound := ⟨true,false,⟨⟨(360691/471338),0,0,(44649/471338)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(1077/2570),0,0,(-1/7710)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
private abbrev sourceBound295 : CertBound := ⟨true,false,⟨⟨(10943/4454),0,0,(-567/4454)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
private abbrev sourceBound429 : CertBound := ⟨true,true,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private abbrev sourceBound439 : CertBound := ⟨true,true,⟨⟨(2524837/1683350),0,0,(312543/1683350)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(1077/2570),0,0,(-1/7710)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
private abbrev sourceBound819 : CertBound := ⟨false,false,⟨⟨(6293/11390),0,0,(931/34170)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private abbrev sourceBound836 : CertBound := ⟨false,false,⟨⟨(25/34),0,0,(-5/102)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private abbrev sourceBound855 : CertBound := ⟨false,false,⟨⟨(2524837/1683350),0,0,(312543/1683350)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(1077/2570),0,0,(-1/7710)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
private abbrev sourceBound863 : CertBound := ⟨false,false,⟨⟨(10943/4454),0,0,(-567/4454)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
private abbrev sourceBound879 : CertBound := ⟨false,true,⟨⟨(-3036789/2641826),(2743163/2641826),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private abbrev sourceBound881 : CertBound := ⟨false,true,⟨⟨(-469528/424787),(1290005/1274361),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private abbrev sourceBound883 : CertBound := ⟨false,true,⟨⟨(-3513140/3269013),(1085402/1089671),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private abbrev sourceBound891 : CertBound := ⟨false,true,⟨⟨(-6400129/17171869),(10602568/17171869),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private abbrev sourceBound892 : CertBound := ⟨false,true,⟨⟨(-5821373/16566693),(3338245/5522231),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private abbrev sourceBound894 : CertBound := ⟨false,true,⟨⟨(-13630693/42497169),(25001788/42497169),0,0⟩,⟨(42/143),(1/429),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
private abbrev sourceBound1139 : CertBound := ⟨false,true,⟨⟨(4495/15946),0,0,(95/6834)⟩,⟨(39/134),0,0,(1/402)⟩,⟨(15/34),0,0,(-1/34)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩⟩⟩
private abbrev sourceBound1161 : CertBound := ⟨false,true,⟨⟨(360691/471338),0,0,(44649/471338)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(1077/2570),0,0,(-1/7710)⟩,⟨(27/118),0,0,(1/118)⟩,⟨(1191/4442),0,0,(-1/13326)⟩⟩⟩
private abbrev sourceBound1182 : CertBound := ⟨false,true,⟨⟨(512500281/379870139),(-138101956/379870139),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
private abbrev sourceBound1183 : CertBound := ⟨false,true,⟨⟨(2318149/1716605),(-374222/1029963),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
private abbrev sourceBound1184 : CertBound := ⟨false,true,⟨⟨(15941/11638),(-10944/29095),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(89/214),(1/214),0,0⟩⟩⟩
open Freiman
namespace BatchLookup17
set_option maxRecDepth 30000
set_option maxHeartbeats 0
private def path129 : LowerHistoryPath := ⟨.left,129,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,16⟩
end BatchLookup17

-- Compact selected bound lookup machinery.
open Freiman
namespace BoundCompact16
set_option maxRecDepth 30000

private def emptyBound : CertBound :=
  ⟨true,false,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

private theorem bound_of_option (id : ℕ) (target : CertBound)
    (h : lowerHistoryBounds[id - 1]? = some target) :
    lowerHistoryBound id = target := by
  unfold lowerHistoryBound
  exact (congrArg (fun o : Option CertBound => o.getD emptyBound) h).trans rfl

private theorem size01 : lowerHistoryBounds01.size = 200 := by rfl
private theorem size02 : lowerHistoryBounds02.size = 200 := by rfl
private theorem size03 : lowerHistoryBounds03.size = 200 := by rfl
private theorem size04 : lowerHistoryBounds04.size = 200 := by rfl
private theorem size05 : lowerHistoryBounds05.size = 200 := by rfl

private theorem global_to_chunk1 (i : ℕ) (hi : i < 200) :
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

private theorem global_to_chunk2 (i : ℕ) (hi : i < 200) :
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

private theorem global_to_chunk3 (i : ℕ) (hi : i < 200) :
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

private theorem global_to_chunk4 (i : ℕ) (hi : i < 200) :
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

private theorem global_to_chunk5 (i : ℕ) (hi : i < 200) :
    lowerHistoryBounds[800 + i]? = lowerHistoryBounds05[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_left (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04]
  exact congrArg (fun j => lowerHistoryBounds05[j]?) (by omega)

private theorem global_to_chunk6 (i : ℕ) :
    lowerHistoryBounds[1000 + i]? = lowerHistoryBounds06[i]? := by
  unfold lowerHistoryBounds
  rw [Array.getElem?_append_right (xs := lowerHistoryBounds01 ++ lowerHistoryBounds02 ++ lowerHistoryBounds03 ++ lowerHistoryBounds04 ++ lowerHistoryBounds05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04, size05]
  exact congrArg (fun j => lowerHistoryBounds06[j]?) (by omega)

end BoundCompact16

namespace BatchLookup17
private theorem bound3 : lowerHistoryBound 3 = sourceBound3 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[2]? = some sourceBound3 := Eq.refl (some sourceBound3)
  exact (BoundCompact16.global_to_chunk1 2 (by decide)).trans hlocal
private theorem bound8 : lowerHistoryBound 8 = sourceBound8 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[7]? = some sourceBound8 := Eq.refl (some sourceBound8)
  exact (BoundCompact16.global_to_chunk1 7 (by decide)).trans hlocal
private theorem bound21 : lowerHistoryBound 21 = sourceBound21 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[20]? = some sourceBound21 := Eq.refl (some sourceBound21)
  exact (BoundCompact16.global_to_chunk1 20 (by decide)).trans hlocal
private theorem bound34 : lowerHistoryBound 34 = sourceBound34 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[33]? = some sourceBound34 := Eq.refl (some sourceBound34)
  exact (BoundCompact16.global_to_chunk1 33 (by decide)).trans hlocal
private theorem bound136 : lowerHistoryBound 136 = sourceBound136 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[135]? = some sourceBound136 := Eq.refl (some sourceBound136)
  exact (BoundCompact16.global_to_chunk1 135 (by decide)).trans hlocal
private theorem bound180 : lowerHistoryBound 180 = sourceBound180 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[179]? = some sourceBound180 := Eq.refl (some sourceBound180)
  exact (BoundCompact16.global_to_chunk1 179 (by decide)).trans hlocal
private theorem bound191 : lowerHistoryBound 191 = sourceBound191 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[190]? = some sourceBound191 := Eq.refl (some sourceBound191)
  exact (BoundCompact16.global_to_chunk1 190 (by decide)).trans hlocal
private theorem bound260 : lowerHistoryBound 260 = sourceBound260 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[59]? = some sourceBound260 := Eq.refl (some sourceBound260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hlocal
private theorem bound267 : lowerHistoryBound 267 = sourceBound267 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[66]? = some sourceBound267 := Eq.refl (some sourceBound267)
  exact (BoundCompact16.global_to_chunk2 66 (by decide)).trans hlocal
private theorem bound275 : lowerHistoryBound 275 = sourceBound275 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[74]? = some sourceBound275 := Eq.refl (some sourceBound275)
  exact (BoundCompact16.global_to_chunk2 74 (by decide)).trans hlocal
private theorem bound371 : lowerHistoryBound 371 = sourceBound371 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[170]? = some sourceBound371 := Eq.refl (some sourceBound371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hlocal
private theorem bound376 : lowerHistoryBound 376 = sourceBound376 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[175]? = some sourceBound376 := Eq.refl (some sourceBound376)
  exact (BoundCompact16.global_to_chunk2 175 (by decide)).trans hlocal
private theorem bound385 : lowerHistoryBound 385 = sourceBound385 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[184]? = some sourceBound385 := Eq.refl (some sourceBound385)
  exact (BoundCompact16.global_to_chunk2 184 (by decide)).trans hlocal
private theorem bound416 : lowerHistoryBound 416 = sourceBound416 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[15]? = some sourceBound416 := Eq.refl (some sourceBound416)
  exact (BoundCompact16.global_to_chunk3 15 (by decide)).trans hlocal
private theorem bound420 : lowerHistoryBound 420 = sourceBound420 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[19]? = some sourceBound420 := Eq.refl (some sourceBound420)
  exact (BoundCompact16.global_to_chunk3 19 (by decide)).trans hlocal
private theorem bound440 : lowerHistoryBound 440 = sourceBound440 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[39]? = some sourceBound440 := Eq.refl (some sourceBound440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hlocal
private theorem bound545 : lowerHistoryBound 545 = sourceBound545 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[144]? = some sourceBound545 := Eq.refl (some sourceBound545)
  exact (BoundCompact16.global_to_chunk3 144 (by decide)).trans hlocal
private theorem bound560 : lowerHistoryBound 560 = sourceBound560 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[159]? = some sourceBound560 := Eq.refl (some sourceBound560)
  exact (BoundCompact16.global_to_chunk3 159 (by decide)).trans hlocal
private theorem bound591 : lowerHistoryBound 591 = sourceBound591 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[190]? = some sourceBound591 := Eq.refl (some sourceBound591)
  exact (BoundCompact16.global_to_chunk3 190 (by decide)).trans hlocal
private theorem bound649 : lowerHistoryBound 649 = sourceBound649 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[48]? = some sourceBound649 := Eq.refl (some sourceBound649)
  exact (BoundCompact16.global_to_chunk4 48 (by decide)).trans hlocal
private theorem bound663 : lowerHistoryBound 663 = sourceBound663 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[62]? = some sourceBound663 := Eq.refl (some sourceBound663)
  exact (BoundCompact16.global_to_chunk4 62 (by decide)).trans hlocal
private theorem bound711 : lowerHistoryBound 711 = sourceBound711 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[110]? = some sourceBound711 := Eq.refl (some sourceBound711)
  exact (BoundCompact16.global_to_chunk4 110 (by decide)).trans hlocal
private theorem bound746 : lowerHistoryBound 746 = sourceBound746 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[145]? = some sourceBound746 := Eq.refl (some sourceBound746)
  exact (BoundCompact16.global_to_chunk4 145 (by decide)).trans hlocal
private theorem bound772 : lowerHistoryBound 772 = sourceBound772 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[171]? = some sourceBound772 := Eq.refl (some sourceBound772)
  exact (BoundCompact16.global_to_chunk4 171 (by decide)).trans hlocal
private theorem bound780 : lowerHistoryBound 780 = sourceBound780 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[179]? = some sourceBound780 := Eq.refl (some sourceBound780)
  exact (BoundCompact16.global_to_chunk4 179 (by decide)).trans hlocal
private theorem bound781 : lowerHistoryBound 781 = sourceBound781 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[180]? = some sourceBound781 := Eq.refl (some sourceBound781)
  exact (BoundCompact16.global_to_chunk4 180 (by decide)).trans hlocal
private theorem bound821 : lowerHistoryBound 821 = sourceBound821 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[20]? = some sourceBound821 := Eq.refl (some sourceBound821)
  exact (BoundCompact16.global_to_chunk5 20 (by decide)).trans hlocal
private theorem bound843 : lowerHistoryBound 843 = sourceBound843 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[42]? = some sourceBound843 := Eq.refl (some sourceBound843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hlocal
private theorem bound845 : lowerHistoryBound 845 = sourceBound845 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[44]? = some sourceBound845 := Eq.refl (some sourceBound845)
  exact (BoundCompact16.global_to_chunk5 44 (by decide)).trans hlocal
private theorem bound856 : lowerHistoryBound 856 = sourceBound856 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[55]? = some sourceBound856 := Eq.refl (some sourceBound856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hlocal
private theorem bound876 : lowerHistoryBound 876 = sourceBound876 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[75]? = some sourceBound876 := Eq.refl (some sourceBound876)
  exact (BoundCompact16.global_to_chunk5 75 (by decide)).trans hlocal
private theorem bound957 : lowerHistoryBound 957 = sourceBound957 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[156]? = some sourceBound957 := Eq.refl (some sourceBound957)
  exact (BoundCompact16.global_to_chunk5 156 (by decide)).trans hlocal
private theorem bound1025 : lowerHistoryBound 1025 = sourceBound1025 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[24]? = some sourceBound1025 := Eq.refl (some sourceBound1025)
  exact (BoundCompact16.global_to_chunk6 24).trans hlocal
private theorem bound1037 : lowerHistoryBound 1037 = sourceBound1037 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[36]? = some sourceBound1037 := Eq.refl (some sourceBound1037)
  exact (BoundCompact16.global_to_chunk6 36).trans hlocal
private theorem bound1046 : lowerHistoryBound 1046 = sourceBound1046 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[45]? = some sourceBound1046 := Eq.refl (some sourceBound1046)
  exact (BoundCompact16.global_to_chunk6 45).trans hlocal
private theorem bound1146 : lowerHistoryBound 1146 = sourceBound1146 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[145]? = some sourceBound1146 := Eq.refl (some sourceBound1146)
  exact (BoundCompact16.global_to_chunk6 145).trans hlocal
private theorem bound1153 : lowerHistoryBound 1153 = sourceBound1153 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[152]? = some sourceBound1153 := Eq.refl (some sourceBound1153)
  exact (BoundCompact16.global_to_chunk6 152).trans hlocal
private theorem bound1157 : lowerHistoryBound 1157 = sourceBound1157 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[156]? = some sourceBound1157 := Eq.refl (some sourceBound1157)
  exact (BoundCompact16.global_to_chunk6 156).trans hlocal
end BatchLookup17

open Freiman
namespace SourceValues17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem source129 : lowerHistorySourcePremises BatchLookup17.path129 =
    ([[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound1153 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound1146 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound1037 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound1025 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound1153 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound1146 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound1037 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound180 (congrArg₂ List.cons BatchLookup17.bound649 (congrArg₂ List.cons BatchLookup17.bound560 (congrArg₂ List.cons BatchLookup17.bound1046 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound1153 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound1146 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound191 (congrArg₂ List.cons BatchLookup17.bound845 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound1025 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound1153 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound1146 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound191 (congrArg₂ List.cons BatchLookup17.bound845 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound180 (congrArg₂ List.cons BatchLookup17.bound649 (congrArg₂ List.cons BatchLookup17.bound560 (congrArg₂ List.cons BatchLookup17.bound1046 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound1153 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound267 (congrArg₂ List.cons BatchLookup17.bound821 (congrArg₂ List.cons BatchLookup17.bound772 (congrArg₂ List.cons BatchLookup17.bound1157 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound1037 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound1025 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound1153 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound267 (congrArg₂ List.cons BatchLookup17.bound821 (congrArg₂ List.cons BatchLookup17.bound772 (congrArg₂ List.cons BatchLookup17.bound1157 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound1037 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound180 (congrArg₂ List.cons BatchLookup17.bound649 (congrArg₂ List.cons BatchLookup17.bound560 (congrArg₂ List.cons BatchLookup17.bound1046 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound1153 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound267 (congrArg₂ List.cons BatchLookup17.bound821 (congrArg₂ List.cons BatchLookup17.bound772 (congrArg₂ List.cons BatchLookup17.bound1157 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound191 (congrArg₂ List.cons BatchLookup17.bound845 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound1025 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound1153 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound267 (congrArg₂ List.cons BatchLookup17.bound821 (congrArg₂ List.cons BatchLookup17.bound772 (congrArg₂ List.cons BatchLookup17.bound1157 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound191 (congrArg₂ List.cons BatchLookup17.bound845 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound180 (congrArg₂ List.cons BatchLookup17.bound649 (congrArg₂ List.cons BatchLookup17.bound560 (congrArg₂ List.cons BatchLookup17.bound1046 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound275 (congrArg₂ List.cons BatchLookup17.bound876 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound1146 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound1037 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound1025 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound275 (congrArg₂ List.cons BatchLookup17.bound876 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound1146 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound1037 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound180 (congrArg₂ List.cons BatchLookup17.bound649 (congrArg₂ List.cons BatchLookup17.bound560 (congrArg₂ List.cons BatchLookup17.bound1046 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound275 (congrArg₂ List.cons BatchLookup17.bound876 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound1146 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound191 (congrArg₂ List.cons BatchLookup17.bound845 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound1025 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound275 (congrArg₂ List.cons BatchLookup17.bound876 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound1146 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound191 (congrArg₂ List.cons BatchLookup17.bound845 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound180 (congrArg₂ List.cons BatchLookup17.bound649 (congrArg₂ List.cons BatchLookup17.bound560 (congrArg₂ List.cons BatchLookup17.bound1046 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound275 (congrArg₂ List.cons BatchLookup17.bound876 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound267 (congrArg₂ List.cons BatchLookup17.bound821 (congrArg₂ List.cons BatchLookup17.bound772 (congrArg₂ List.cons BatchLookup17.bound1157 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound1037 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound1025 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound275 (congrArg₂ List.cons BatchLookup17.bound876 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound267 (congrArg₂ List.cons BatchLookup17.bound821 (congrArg₂ List.cons BatchLookup17.bound772 (congrArg₂ List.cons BatchLookup17.bound1157 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound1037 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound180 (congrArg₂ List.cons BatchLookup17.bound649 (congrArg₂ List.cons BatchLookup17.bound560 (congrArg₂ List.cons BatchLookup17.bound1046 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound275 (congrArg₂ List.cons BatchLookup17.bound876 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound267 (congrArg₂ List.cons BatchLookup17.bound821 (congrArg₂ List.cons BatchLookup17.bound772 (congrArg₂ List.cons BatchLookup17.bound1157 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound191 (congrArg₂ List.cons BatchLookup17.bound845 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound1025 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound275 (congrArg₂ List.cons BatchLookup17.bound876 (congrArg₂ List.cons BatchLookup17.bound420 (congrArg₂ List.cons BatchLookup17.bound780 (congrArg₂ List.cons BatchLookup17.bound267 (congrArg₂ List.cons BatchLookup17.bound821 (congrArg₂ List.cons BatchLookup17.bound772 (congrArg₂ List.cons BatchLookup17.bound1157 (congrArg₂ List.cons BatchLookup17.bound416 (congrArg₂ List.cons BatchLookup17.bound746 (congrArg₂ List.cons BatchLookup17.bound781 (congrArg₂ List.cons BatchLookup17.bound8 (congrArg₂ List.cons BatchLookup17.bound711 (congrArg₂ List.cons BatchLookup17.bound34 (congrArg₂ List.cons BatchLookup17.bound191 (congrArg₂ List.cons BatchLookup17.bound845 (congrArg₂ List.cons BatchLookup17.bound385 (congrArg₂ List.cons BatchLookup17.bound591 (congrArg₂ List.cons BatchLookup17.bound180 (congrArg₂ List.cons BatchLookup17.bound649 (congrArg₂ List.cons BatchLookup17.bound560 (congrArg₂ List.cons BatchLookup17.bound1046 (congrArg₂ List.cons BatchLookup17.bound376 (congrArg₂ List.cons BatchLookup17.bound545 (congrArg₂ List.cons BatchLookup17.bound663 (congrArg₂ List.cons BatchLookup17.bound957 (congrArg₂ List.cons BatchLookup17.bound136 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))))))))))))))))
  exact SourceMemo17_129.source.trans hb.symm
end SourceValues17


namespace PremiseCompact50

variable {α : Type} (a b c d e f : Array α)
  (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200)
  (hd : d.size = 200) (he : e.size = 200)
include ha hb hc hd he

end PremiseCompact50

open Freiman
namespace BatchLookup17
set_option maxRecDepth 30000
private theorem size01 : lowerHistoryPremises01.size = 200 := by rfl
private theorem size02 : lowerHistoryPremises02.size = 200 := by rfl
private theorem size03 : lowerHistoryPremises03.size = 200 := by rfl
private theorem size04 : lowerHistoryPremises04.size = 200 := by rfl
private theorem size05 : lowerHistoryPremises05.size = 200 := by rfl
end BatchLookup17

open Freiman
namespace BatchFacts15

end BatchFacts15

open Freiman BatchFacts15
namespace ExtrasMemo17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,138,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),false)],([2,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
private def expected : List (List CertBound) := [
[sourceBound836,sourceBound1139,sourceBound863,sourceBound1161,sourceBound881],
[sourceBound836,sourceBound1139,sourceBound863,sourceBound285,sourceBound879],
[sourceBound836,sourceBound1139,sourceBound295,sourceBound439,sourceBound881],
[sourceBound836,sourceBound1139,sourceBound295,sourceBound855,sourceBound883],
[sourceBound836,sourceBound259,sourceBound863,sourceBound1161,sourceBound1184],
[sourceBound836,sourceBound259,sourceBound863,sourceBound285,sourceBound1182],
[sourceBound836,sourceBound259,sourceBound295,sourceBound439,sourceBound1184],
[sourceBound836,sourceBound259,sourceBound295,sourceBound855,sourceBound1183],
[sourceBound284,sourceBound429,sourceBound863,sourceBound1161,sourceBound881],
[sourceBound284,sourceBound429,sourceBound863,sourceBound285,sourceBound879],
[sourceBound284,sourceBound429,sourceBound295,sourceBound439,sourceBound881],
[sourceBound284,sourceBound429,sourceBound295,sourceBound855,sourceBound883],
[sourceBound284,sourceBound819,sourceBound863,sourceBound1161,sourceBound892],
[sourceBound284,sourceBound819,sourceBound863,sourceBound285,sourceBound891],
[sourceBound284,sourceBound819,sourceBound295,sourceBound439,sourceBound892],
[sourceBound284,sourceBound819,sourceBound295,sourceBound855,sourceBound894]
]
end ExtrasMemo17

open Freiman
namespace ExtraValues17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
end ExtraValues17

open Freiman
namespace BatchCoverage15

end BatchCoverage15

open Freiman BatchLookup17 BatchCoverage15
namespace BatchCoverageAll17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
end BatchCoverageAll17

open Freiman BatchLookup17
namespace PathLookup17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
end PathLookup17

-- Reduce the global witness array structurally, then
-- let the kernel inspect only the selected entry of its 200-element chunk.
open Freiman
namespace WitnessCompact16
set_option maxRecDepth 30000

private theorem size01 : lowerHistoryWitnesses01.size = 200 := by rfl
private theorem size02 : lowerHistoryWitnesses02.size = 200 := by rfl
private theorem size03 : lowerHistoryWitnesses03.size = 200 := by rfl
private theorem size04 : lowerHistoryWitnesses04.size = 200 := by rfl
private theorem size05 : lowerHistoryWitnesses05.size = 200 := by rfl

private theorem global_to_chunk1 (i : ℕ) (hi : i < 200) :
    lowerHistoryWitnesses[i]? = lowerHistoryWitnesses01[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02)
    (by simp only [Array.size_append, size01, size02]; omega)]
  exact Array.getElem?_append_left (by rw [size01]; omega)

private theorem global_to_chunk2 (i : ℕ) (hi : i < 200) :
    lowerHistoryWitnesses[200 + i]? = lowerHistoryWitnesses02[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02)
    (by simp only [Array.size_append, size01, size02]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01) (by rw [size01]; omega), size01]
  exact congrArg (fun j => lowerHistoryWitnesses02[j]?) (by omega)

private theorem global_to_chunk5 (i : ℕ) (hi : i < 200) :
    lowerHistoryWitnesses[800 + i]? = lowerHistoryWitnesses05[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04]
  exact congrArg (fun j => lowerHistoryWitnesses05[j]?) (by omega)

private theorem global_to_chunk6 (i : ℕ) :
    lowerHistoryWitnesses[1000 + i]? = lowerHistoryWitnesses06[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04, size05]
  exact congrArg (fun j => lowerHistoryWitnesses06[j]?) (by omega)

private theorem global_to_chunk3 (i : ℕ) (hi : i < 200) :
    lowerHistoryWitnesses[400 + i]? = lowerHistoryWitnesses03[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02)
    (by simp only [Array.size_append, size01, size02]; omega)]
  simp only [Array.size_append, size01, size02]
  exact congrArg (fun j => lowerHistoryWitnesses03[j]?) (by omega)

private theorem global_to_chunk4 (i : ℕ) (hi : i < 200) :
    lowerHistoryWitnesses[600 + i]? = lowerHistoryWitnesses04[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  rw [Array.getElem?_append_left (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04)
    (by simp only [Array.size_append, size01, size02, size03, size04]; omega)]
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03)
    (by simp only [Array.size_append, size01, size02, size03]; omega)]
  simp only [Array.size_append, size01, size02, size03]
  exact congrArg (fun j => lowerHistoryWitnesses04[j]?) (by omega)

end WitnessCompact16

namespace WitnessLookup17
end WitnessLookup17

open Freiman
namespace BindingIds19
set_option Elab.async false
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

private instance survivorDecidable (p : LowerHistoryPath) : Decidable (lowerHistorySurvivor p) := by
  unfold lowerHistorySurvivor
  infer_instance

end BindingIds19

open Freiman BatchLookup17 BindingIds19
namespace BatchIdSolution100
set_option maxRecDepth 30000
set_option maxHeartbeats 0
end BatchIdSolution100
theorem _root_.solution : lowerHistorySourcePremises (⟨.left,129,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,16⟩ : LowerHistoryPath) =
    ([[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,1146,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,1153,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,1146,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,1037,385,591,180,649,560,1046,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,1025,376,545,663,957,136],[371,843,260,440,3,856,21,275,876,420,780,267,821,772,1157,416,746,781,8,711,34,191,845,385,591,180,649,560,1046,376,545,663,957,136]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  exact SourceValues17.source129
end M7Binding100Sep15
#print axioms solution
