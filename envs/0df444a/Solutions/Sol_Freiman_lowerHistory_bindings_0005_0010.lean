-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0005_0010
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-17T13:49:21.804832+00:00
-- url     : https://prove2.me/submissions/be61394a-9c27-4b6e-afaf-5e5e960afb8a

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
namespace M7Binding0Sep15
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
namespace BindingNumeric20
set_option Elab.async false
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
private theorem norm2 : lowerHistoryNormalization ([2,3],[3,1]) false false = ⟨false,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm9 : lowerHistoryNormalization ([2,3,1],[3,1]) false false = ⟨false,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm11 : lowerHistoryNormalization ([2,3,1,1],[3,1]) true false = ⟨true,false,⟨⟨(1607/35615),0,0,(208/35615)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(373/838),0,0,(-1/838)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm12 : lowerHistoryNormalization ([2,2],[3,1]) true false = ⟨true,false,⟨⟨(753/1394),0,0,(91/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm13 : lowerHistoryNormalization ([2,2],[3,1]) false false = ⟨false,false,⟨⟨(753/1394),0,0,(91/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm14 : lowerHistoryNormalization ([2,2,3],[3,1]) true true = ⟨true,true,⟨⟨(3687/48134),0,0,(31/48134)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm15 : lowerHistoryNormalization ([2,2,3,1],[3,1]) true true = ⟨true,true,⟨⟨(453/8815),0,0,(-254/61705)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(177/430),0,0,(-1/3010)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm16 : lowerHistoryNormalization ([2,2,2],[3,1]) true true = ⟨true,true,⟨⟨(767/8399),0,0,(96/8399)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm17 : lowerHistoryNormalization ([2,2,2,1],[3,1]) true true = ⟨true,true,⟨⟨(2419/55870),0,0,(169/55870)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(629/1510),0,0,(-1/1510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm18 : lowerHistoryNormalization ([2,2,1],[3,1]) true false = ⟨true,false,⟨⟨(1167/4454),0,0,(71/4454)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm19 : lowerHistoryNormalization ([2,2,1,1],[3,1]) true true = ⟨true,true,⟨⟨(887/11135),0,0,(112/11135)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(73/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey0 : lowerHistoryPull (lowerHistoryH7) ([2],[3]) false = ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey1 : lowerHistoryPull (lowerHistoryH9) ([2],[3]) false = ⟨false,false,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey22 : lowerHistoryPull (lowerHistoryH7) ([2,3,1,1],[3,1]) true = ⟨false,false,⟨⟨(1770570100/4981629103),(-500309550/4981629103),0,0⟩,⟨(2000/4561),(1/4561),0,0⟩,⟨(2815/6406),(-1/6406),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey23 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,3,1,1],[3,1]) true = ⟨false,true,⟨⟨(1482277/29217766),(2590429/87653298),0,0⟩,⟨(2000/4561),(1/4561),0,0⟩,⟨(2815/6406),(-1/6406),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey24 : lowerHistoryPull (lowerHistoryHN) ([2,3,1,1],[3,1]) true = ⟨true,false,⟨⟨(1607/35615),0,0,(208/35615)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(373/838),0,0,(-1/838)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey30 : lowerHistoryPull (lowerHistoryH7) ([2,2],[3,1]) true = ⟨false,false,⟨⟨(304094050/73779101),(-85358650/73779101),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey31 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,2],[3,1]) true = ⟨false,true,⟨⟨(128103/216361),(223856/649083),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey32 : lowerHistoryPull (lowerHistoryHN) ([2,2],[3,1]) true = ⟨true,false,⟨⟨(753/1394),0,0,(91/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey33 : lowerHistoryPull (lowerHistoryH7) ([2,2],[3,1]) false = ⟨true,false,⟨⟨(27904867/127104900),(6016573/127104900),0,0⟩,⟨(89/218),(1/654),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey34 : lowerHistoryPull (lowerHistoryH2) ([2,2,3],[3,1]) true = ⟨false,true,⟨⟨(268142813350/2731343647201),(5462261750/8194030941603),0,0⟩,⟨(12645/30862),(-1/30862),0,0⟩,⟨(11607/28307),(1/84921),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey35 : lowerHistoryPull (lowerHistoryH7) ([2,2,3,1],[3,1]) true = ⟨false,false,⟨⟨(1301767350/8029318649),(-1114142900/24087955947),0,0⟩,⟨(1307/3191),(1/9573),0,0⟩,⟨(6051/14758),(-1/14758),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey36 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,2,3,1],[3,1]) true = ⟨false,true,⟨⟨(3239071/141278334),(1887079/141278334),0,0⟩,⟨(1307/3191),(1/9573),0,0⟩,⟨(6051/14758),(-1/14758),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey37 : lowerHistoryPull (lowerHistoryHN) ([2,2,3,1],[3,1]) true = ⟨true,false,⟨⟨(453/8815),0,0,(-254/61705)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(177/430),0,0,(-1/3010)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey38 : lowerHistoryPull (lowerHistoryH9) ([2,2],[3,1]) false = ⟨false,false,⟨⟨(16701/5317),(-7898/5317),0,0⟩,⟨(9/26),(1/26),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey39 : lowerHistoryPull (lowerHistoryH2) ([2,2,2],[3,1]) true = ⟨false,true,⟨⟨(82907566100/478723971011),(506816000/478723971011),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(19695/47641),(1/47641),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey40 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,2,2],[3,1]) true = ⟨false,false,⟨⟨(1259317038500/5655451533237),(23941271500/5655451533237),0,0⟩,⟨(19695/47641),(1/47641),0,0⟩,⟨(986/2377),(-1/2377),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey41 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,2,2],[3,1]) true = ⟨false,false,⟨⟨(11734367/160933828),(8407790/120700371),0,0⟩,⟨(427/1034),(1/3102),0,0⟩,⟨(32284/77821),(-1/77821),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey42 : lowerHistoryPull (lowerHistoryH23) ([2,2,2],[3,1]) true = ⟨false,true,⟨⟨(348634303500/1397799279019),(-16400787500/1397799279019),0,0⟩,⟨(19695/47641),(1/47641),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey43 : lowerHistoryPull (lowerHistoryH7) ([2,2,2,1],[3,1]) true = ⟨false,false,⟨⟨(36750350/129312749),(-114970050/1422440239),0,0⟩,⟨(2283/5533),(1/5533),0,0⟩,⟨(3428/8293),(-1/8293),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey44 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,2,2,1],[3,1]) true = ⟨false,true,⟨⟨(1849741/45885169),(3232852/137655507),0,0⟩,⟨(2283/5533),(1/5533),0,0⟩,⟨(3428/8293),(-1/8293),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey45 : lowerHistoryPull (lowerHistoryHN) ([2,2,2,1],[3,1]) true = ⟨true,false,⟨⟨(2419/55870),0,0,(169/55870)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(629/1510),0,0,(-1/1510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey46 : lowerHistoryPull (lowerHistoryH2) ([2,2,1],[3,1]) true = ⟨false,true,⟨⟨(68586194850/178709345581),(991451750/536128036743),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(8849/21061),(1/21061),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey47 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,2,1],[3,1]) true = ⟨false,false,⟨⟨(29268009500/55044587319),(817282000/495401285871),0,0⟩,⟨(8849/21061),(1/21061),0,0⟩,⟨(133/314),(-1/942),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey48 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,2,1],[3,1]) true = ⟨false,false,⟨⟨(3863074/21797711),(14465535/87190844),0,0⟩,⟨(594/1417),(1/1417),0,0⟩,⟨(13033/30766),(-1/30766),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey49 : lowerHistoryPull (lowerHistoryH23) ([2,2,1],[3,1]) true = ⟨false,true,⟨⟨(151698148500/261719550079),(-11626862500/261719550079),0,0⟩,⟨(8849/21061),(1/21061),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey50 : lowerHistoryPull (lowerHistoryH7) ([2,2,1,1],[3,1]) true = ⟨false,false,⟨⟨(337287600/542022569),(-286182650/1626067707),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(515/1226),(-1/3678),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey51 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,2,1,1],[3,1]) true = ⟨false,true,⟨⟨(846361/9537054),(493039/9537054),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(515/1226),(-1/3678),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey52 : lowerHistoryPull (lowerHistoryHN) ([2,2,1,1],[3,1]) true = ⟨true,false,⟨⟨(887/11135),0,0,(112/11135)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(73/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pull1 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = ⟨true,true,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey1]
  rfl
private theorem pull36 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH7) ([2,2],[3,1]) false = ⟨false,true,⟨⟨(27904867/127104900),(6016573/127104900),0,0⟩,⟨(89/218),(1/654),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey33]
  rfl
private theorem pull44 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,2,2],[3,1]) true = ⟨true,false,⟨⟨(82907566100/478723971011),(506816000/478723971011),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(19695/47641),(1/47641),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey39]
  rfl
private theorem pull52 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,2,1],[3,1]) true = ⟨true,false,⟨⟨(68586194850/178709345581),(991451750/536128036743),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(8849/21061),(1/21061),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey46]
  rfl
end BindingNumeric20
set_option Elab.async false

open Freiman
namespace BindingSourceBranches20
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem branchesG0 :
    (lowerHistoryNecessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[1]),true)⟩ ([2,3],[3,1]) = some [⟨false,false,⟨⟨(911720/2447159),(6369548/7341477),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [⟨true,false,⟨⟨(-2415463/5270749),(1816717/5270749),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,3,3],[3,1]) = some [⟨false,false,⟨⟨(15846/447863),(105176/1343589),0,0⟩,⟨(529/1222),(1/1222),0,0⟩,⟨(8265/19058),(-1/57174),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,3,1],[3,1]) = some [⟨false,false,⟨⟨(2496968/95947501),(5603863/287842503),0,0⟩,⟨(8265/19058),(-1/57174),0,0⟩,⟨(4367/10069),(1/10069),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,3,2],[3,1]) = some [⟨false,false,⟨⟨(482605/7364591),(3580367/22093773),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,2,1],[3,1]) = some [⟨false,false,⟨⟨(2664700/82712279),(5005419/82712279),0,0⟩,⟨(2455/5638),(1/5638),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,3,1],[3,1]) = some [⟨false,false,⟨⟨(534009/1863433),(1199347/5590299),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
  decide +kernel
private theorem branchesG1 :
    (lowerHistoryNecessary ⟨⟨([1,2,3,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,1,1],[3,1]) = some [⟨false,false,⟨⟨(661229/9815663),(4179215/29446989),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,3,1],[3,1]) = some [⟨true,false,⟨⟨(-2957543/15273863),(2209052/15273863),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3,1,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,3,1,2],[3,1]) = some [⟨false,false,⟨⟨(41681/1638923),(357512/4916769),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,3,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,3,1,1],[3,1]) = some [⟨false,false,⟨⟨(661229/9815663),(4179215/29446989),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[1]),true)⟩ ([2,2],[3,1]) = some [⟨false,false,⟨⟨(21019/31993),(166288/95979),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [⟨true,false,⟨⟨(-4078497/4976303),(3063403/4976303),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,2,3],[3,1]) = some [⟨false,false,⟨⟨(1397574/21865727),(9535016/65597181),0,0⟩,⟨(89/218),(1/654),0,0⟩,⟨(12645/30862),(-1/30862),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,3,1],[3,1]) = some [⟨false,false,⟨⟨(52522166/1090678511),(39307153/1090678511),0,0⟩,⟨(12645/30862),(-1/30862),0,0⟩,⟨(2228/5437),(1/5437),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
  decide +kernel
private theorem branchesG2 :
    (lowerHistoryNecessary ⟨⟨([1,2,2,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,2,2],[3,1]) = some [⟨false,false,⟨⟨(765379/6640933),(1959179/6640933),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,2,1],[3,1]) = some [⟨false,false,⟨⟨(494058/8394529),(2764045/25183587),0,0⟩,⟨(427/1034),(1/3102),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [⟨false,false,⟨⟨(254992/735839),(472767/735839),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,1,1],[3,1]) = some [⟨false,false,⟨⟨(6907/57661),(185255/749593),0,0⟩,⟨(594/1417),(1/1417),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,2,1],[3,1]) = some [⟨true,false,⟨⟨(-1707521/5116787),(1276674/5116787),0,0⟩,⟨(594/1417),(1/1417),0,0⟩,⟨(133/314),(-1/942),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2,1,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,2,1,3],[3,1]) = some [⟨false,false,⟨⟨(11612992/441303707),(85271372/1323911121),0,0⟩,⟨(9905/23363),(1/70089),0,0⟩,⟨(617/1453),(-1/1453),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2,1,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,2,1,2],[3,1]) = some [⟨false,false,⟨⟨(272925/6149533),(2298646/18448599),0,0⟩,⟨(1272/3013),(1/3013),0,0⟩,⟨(133/314),(-1/942),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,2,1,1],[3,1]) = some [⟨false,false,⟨⟨(6907/57661),(185255/749593),0,0⟩,⟨(594/1417),(1/1417),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
  decide +kernel
end BindingSourceBranches20

open Freiman
namespace BindingSourceSupport20
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem relaxed1 : lowerHistoryRelaxedGoodness ⟨([1],[3,1]),(false,false)⟩ = some [⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩] := by
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
private theorem singleton_removeAll_of_mem {a : CertBound} {l : List CertBound}
    (h : a ∈ l) : [a].removeAll l = [] := by
  simp [List.removeAll, h]
end BindingSourceSupport20

open Freiman
open RootOps19
set_option linter.all false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace BindingOps20_6
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b7 : CertBound) (b19 : CertBound) (b21 : CertBound) (b207 : CertBound) (b260 : CertBound) (b275 : CertBound) (b371 : CertBound) (b440 : CertBound) (b442 : CertBound) (b699 : CertBound) (b803 : CertBound) (b807 : CertBound) (b814 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1065 : CertBound)
private def path : LowerHistoryPath := ⟨.left,6,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([1],[]),true)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [b7])
    (hb2 : ops.necessary ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,3,1],[3,1]) = some [b19])
    (hb3 : ops.necessary ⟨⟨([1,2,3,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,3,1,1],[3,1]) = some [b699])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,3],[3,1]) false false = b814)
    (hn4 : ops.normalization ([2,3,1],[3,1]) false false = b807)
    (hn5 : ops.normalization ([2,3,1,1],[3,1]) true false = b207)
    (hn6 : ops.pull (lowerHistoryH7) ([2,3,1,1],[3,1]) true = b803)
    (hn7 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,3,1,1],[3,1]) true = b1065)
    (hn8 : ops.pull (lowerHistoryHN) ([2,3,1,1],[3,1]) true = b207)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b807,b19,b207,b699,b803,b1065,b207].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b807,b19,b207,b699,b803,b1065]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b807,b19,b207,b699,b803,b1065]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([3],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps20_6
namespace BindingOps20_7
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b21 : CertBound) (b260 : CertBound) (b275 : CertBound) (b277 : CertBound) (b371 : CertBound) (b440 : CertBound) (b442 : CertBound) (b827 : CertBound) (b843 : CertBound) (b856 : CertBound) (b870 : CertBound) (b1156 : CertBound)
private def path : LowerHistoryPath := ⟨.left,7,[1],([2],[3]),false,[(([2],[1]),true)],([1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[1]),true)⟩ ([2,2],[3,1]) = some [b827])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,2],[3,1]) true false = b277)
    (hn4 : ops.pull (lowerHistoryH7) ([2,2],[3,1]) true = b870)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,2],[3,1]) true = b1156)
    (hn6 : ops.pull (lowerHistoryHN) ([2,2],[3,1]) true = b277)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b277,b827,b870,b1156,b277].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b277,b827,b870,b1156]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b277,b827,b870,b1156]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([2],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hdone, hchoice0, hdone0, hforced0, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps20_7
namespace BindingOps20_8
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b5 : CertBound) (b21 : CertBound) (b212 : CertBound) (b260 : CertBound) (b275 : CertBound) (b371 : CertBound) (b407 : CertBound) (b408 : CertBound) (b440 : CertBound) (b442 : CertBound) (b675 : CertBound) (b695 : CertBound) (b758 : CertBound) (b817 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1020 : CertBound) (b1096 : CertBound) (b1125 : CertBound)
private def path : LowerHistoryPath := ⟨.left,8,[1],([2],[3]),false,[(([2],[1]),false),(([3],[]),true),(([],[1]),false)],([1,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [b5])
    (hb2 : ops.necessary ⟨⟨([1,2,2,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,2,3],[3,1]) = some [b695])
    (hb3 : ops.necessary ⟨⟨([1,2,2,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,3,1],[3,1]) = some [b675])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,2],[3,1]) false false = b817)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,2],[3,1]) false = b1125)
    (hn5 : ops.normalization ([2,2,3],[3,1]) true true = b408)
    (hn6 : ops.pull (lowerHistoryH2) ([2,2,3],[3,1]) true = b1096)
    (hn7 : ops.normalization ([2,2,3,1],[3,1]) true true = b407)
    (hn8 : ops.pull (lowerHistoryH7) ([2,2,3,1],[3,1]) true = b758)
    (hn9 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,2,3,1],[3,1]) true = b1020)
    (hn10 : ops.pull (lowerHistoryHN) ([2,2,3,1],[3,1]) true = b212)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b408,b695,b1096,b407,b675,b758,b1020,b212].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b408,b695,b1096,b407,b675,b758,b1020,b212]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b408,b695,b1096,b407,b675,b758,b1020,b212]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([2],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH7]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,2,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps20_8
namespace BindingOps20_9
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b5 : CertBound) (b21 : CertBound) (b205 : CertBound) (b243 : CertBound) (b250 : CertBound) (b260 : CertBound) (b275 : CertBound) (b371 : CertBound) (b402 : CertBound) (b411 : CertBound) (b440 : CertBound) (b442 : CertBound) (b693 : CertBound) (b704 : CertBound) (b734 : CertBound) (b775 : CertBound) (b787 : CertBound) (b817 : CertBound) (b843 : CertBound) (b856 : CertBound) (b868 : CertBound) (b1048 : CertBound) (b1113 : CertBound) (b1125 : CertBound) (b1134 : CertBound)
private def path : LowerHistoryPath := ⟨.left,9,[1],([2],[3]),false,[(([2],[1]),false),(([2],[]),true),(([],[1]),false)],([1,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [b5])
    (hb2 : ops.necessary ⟨⟨([1,2,2,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,2,2],[3,1]) = some [b734])
    (hb3 : ops.necessary ⟨⟨([1,2,2,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,2,1],[3,1]) = some [b693])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,2],[3,1]) false false = b817)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,2],[3,1]) false = b1125)
    (hn5 : ops.pull (lowerHistoryH7) ([2,2],[3,1]) false = b250)
    (hn6 : ops.pull (lowerHistoryH9) ([2,2],[3,1]) false = b868)
    (hn7 : ops.normalization ([2,2,2],[3,1]) true true = b411)
    (hn8 : ops.pull (lowerHistoryH2) ([2,2,2],[3,1]) true = b1113)
    (hn9 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,2,2],[3,1]) true = b243)
    (hn10 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,2,2],[3,1]) true = b775)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,2,2],[3,1]) true = b704)
    (hn12 : ops.pull (lowerHistoryH23) ([2,2,2],[3,1]) true = b1134)
    (hn13 : ops.normalization ([2,2,2,1],[3,1]) true true = b402)
    (hn14 : ops.pull (lowerHistoryH7) ([2,2,2,1],[3,1]) true = b787)
    (hn15 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,2,2,1],[3,1]) true = b1048)
    (hn16 : ops.pull (lowerHistoryHN) ([2,2,2,1],[3,1]) true = b205)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b1113,b402,b693,b787,b1048,b205].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205]
] : List (List CertBound))[1])
    (herase2 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b1113,b402,b693,b787,b1048,b205].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205]
] : List (List CertBound))[2])
    (herase3 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205]
] : List (List CertBound))[3])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b1125,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b1113,b402,b693,b787,b1048,b205],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b250,b868,b411,b734,b243,b775,b704,b1134,b402,b693,b787,b1048,b205]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([2],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,2,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1, herase2, herase3]
  rfl
end BindingOps20_9
namespace BindingOps20_10
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b5 : CertBound) (b21 : CertBound) (b224 : CertBound) (b256 : CertBound) (b260 : CertBound) (b265 : CertBound) (b275 : CertBound) (b371 : CertBound) (b409 : CertBound) (b440 : CertBound) (b442 : CertBound) (b738 : CertBound) (b768 : CertBound) (b801 : CertBound) (b815 : CertBound) (b817 : CertBound) (b823 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1087 : CertBound) (b1144 : CertBound) (b1154 : CertBound)
private def path : LowerHistoryPath := ⟨.left,10,[1],([2],[3]),false,[(([2],[1]),false),(([1],[]),true),(([],[1]),false)],([1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,2],[3,1]) = some [b5])
    (hb2 : ops.necessary ⟨⟨([1,2,2,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,2,1],[3,1]) = some [b801])
    (hb3 : ops.necessary ⟨⟨([1,2,2,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,2,1,1],[3,1]) = some [b738])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,2],[3,1]) false false = b817)
    (hn4 : ops.normalization ([2,2,1],[3,1]) true false = b256)
    (hn5 : ops.pull (lowerHistoryH2) ([2,2,1],[3,1]) true = b1144)
    (hn6 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,2,1],[3,1]) true = b265)
    (hn7 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,2,1],[3,1]) true = b815)
    (hn8 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,2,1],[3,1]) true = b768)
    (hn9 : ops.pull (lowerHistoryH23) ([2,2,1],[3,1]) true = b1154)
    (hn10 : ops.normalization ([2,2,1,1],[3,1]) true true = b409)
    (hn11 : ops.pull (lowerHistoryH7) ([2,2,1,1],[3,1]) true = b823)
    (hn12 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,2,1,1],[3,1]) true = b1087)
    (hn13 : ops.pull (lowerHistoryHN) ([2,2,1,1],[3,1]) true = b224)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b256,b801,b1144,b409,b738,b823,b1087,b224].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b256,b801,b1144,b409,b738,b823,b1087,b224],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b256,b801,b265,b815,b768,b1154,b409,b738,b823,b1087,b224]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b256,b801,b265,b815,b768,b1154,b409,b738,b823,b1087,b224].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b256,b801,b1144,b409,b738,b823,b1087,b224],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b256,b801,b265,b815,b768,b1154,b409,b738,b823,b1087,b224]
] : List (List CertBound))[1])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b256,b801,b1144,b409,b738,b823,b1087,b224],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b817,b5,b256,b801,b265,b815,b768,b1154,b409,b738,b823,b1087,b224]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([2],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,2,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1]
  rfl
end BindingOps20_10

open Freiman

private abbrev sourceBound3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩

private abbrev sourceBound5 : CertBound := ⟨true,false,⟨⟨(-4078497/4976303),(3063403/4976303),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private abbrev sourceBound7 : CertBound := ⟨true,false,⟨⟨(-2415463/5270749),(1816717/5270749),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private abbrev sourceBound19 : CertBound := ⟨true,false,⟨⟨(-2957543/15273863),(2209052/15273863),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private abbrev sourceBound21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private abbrev sourceBound205 : CertBound := ⟨true,false,⟨⟨(2419/55870),0,0,(169/55870)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(629/1510),0,0,(-1/1510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound207 : CertBound := ⟨true,false,⟨⟨(1607/35615),0,0,(208/35615)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(373/838),0,0,(-1/838)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound212 : CertBound := ⟨true,false,⟨⟨(453/8815),0,0,(-254/61705)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(177/430),0,0,(-1/3010)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound224 : CertBound := ⟨true,false,⟨⟨(887/11135),0,0,(112/11135)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(73/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound243 : CertBound := ⟨true,false,⟨⟨(82907566100/478723971011),(506816000/478723971011),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(19695/47641),(1/47641),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound250 : CertBound := ⟨true,false,⟨⟨(27904867/127104900),(6016573/127104900),0,0⟩,⟨(89/218),(1/654),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound256 : CertBound := ⟨true,false,⟨⟨(1167/4454),0,0,(71/4454)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound260 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private abbrev sourceBound265 : CertBound := ⟨true,false,⟨⟨(68586194850/178709345581),(991451750/536128036743),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(8849/21061),(1/21061),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound275 : CertBound := ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound277 : CertBound := ⟨true,false,⟨⟨(753/1394),0,0,(91/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound371 : CertBound := ⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

private abbrev sourceBound402 : CertBound := ⟨true,true,⟨⟨(2419/55870),0,0,(169/55870)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(629/1510),0,0,(-1/1510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound407 : CertBound := ⟨true,true,⟨⟨(453/8815),0,0,(-254/61705)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(177/430),0,0,(-1/3010)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound408 : CertBound := ⟨true,true,⟨⟨(3687/48134),0,0,(31/48134)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(487/1174),0,0,(-1/1174)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound409 : CertBound := ⟨true,true,⟨⟨(887/11135),0,0,(112/11135)⟩,⟨(105/262),0,0,(1/262)⟩,⟨(73/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound411 : CertBound := ⟨true,true,⟨⟨(767/8399),0,0,(96/8399)⟩,⟨(29/74),0,0,(1/222)⟩,⟨(193/454),0,0,(-1/454)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private abbrev sourceBound442 : CertBound := ⟨true,true,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound675 : CertBound := ⟨false,false,⟨⟨(52522166/1090678511),(39307153/1090678511),0,0⟩,⟨(12645/30862),(-1/30862),0,0⟩,⟨(2228/5437),(1/5437),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound693 : CertBound := ⟨false,false,⟨⟨(494058/8394529),(2764045/25183587),0,0⟩,⟨(427/1034),(1/3102),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound695 : CertBound := ⟨false,false,⟨⟨(1397574/21865727),(9535016/65597181),0,0⟩,⟨(89/218),(1/654),0,0⟩,⟨(12645/30862),(-1/30862),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound699 : CertBound := ⟨false,false,⟨⟨(661229/9815663),(4179215/29446989),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound704 : CertBound := ⟨false,false,⟨⟨(11734367/160933828),(8407790/120700371),0,0⟩,⟨(427/1034),(1/3102),0,0⟩,⟨(32284/77821),(-1/77821),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound734 : CertBound := ⟨false,false,⟨⟨(765379/6640933),(1959179/6640933),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound738 : CertBound := ⟨false,false,⟨⟨(6907/57661),(185255/749593),0,0⟩,⟨(594/1417),(1/1417),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound758 : CertBound := ⟨false,false,⟨⟨(1301767350/8029318649),(-1114142900/24087955947),0,0⟩,⟨(1307/3191),(1/9573),0,0⟩,⟨(6051/14758),(-1/14758),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound768 : CertBound := ⟨false,false,⟨⟨(3863074/21797711),(14465535/87190844),0,0⟩,⟨(594/1417),(1/1417),0,0⟩,⟨(13033/30766),(-1/30766),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound775 : CertBound := ⟨false,false,⟨⟨(1259317038500/5655451533237),(23941271500/5655451533237),0,0⟩,⟨(19695/47641),(1/47641),0,0⟩,⟨(986/2377),(-1/2377),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private abbrev sourceBound787 : CertBound := ⟨false,false,⟨⟨(36750350/129312749),(-114970050/1422440239),0,0⟩,⟨(2283/5533),(1/5533),0,0⟩,⟨(3428/8293),(-1/8293),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound801 : CertBound := ⟨false,false,⟨⟨(254992/735839),(472767/735839),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound803 : CertBound := ⟨false,false,⟨⟨(1770570100/4981629103),(-500309550/4981629103),0,0⟩,⟨(2000/4561),(1/4561),0,0⟩,⟨(2815/6406),(-1/6406),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound807 : CertBound := ⟨false,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound814 : CertBound := ⟨false,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound815 : CertBound := ⟨false,false,⟨⟨(29268009500/55044587319),(817282000/495401285871),0,0⟩,⟨(8849/21061),(1/21061),0,0⟩,⟨(133/314),(-1/942),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private abbrev sourceBound817 : CertBound := ⟨false,false,⟨⟨(753/1394),0,0,(91/1394)⟩,⟨(29/82),0,0,(1/82)⟩,⟨(19/34),0,0,(-1/34)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound823 : CertBound := ⟨false,false,⟨⟨(337287600/542022569),(-286182650/1626067707),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(515/1226),(-1/3678),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound827 : CertBound := ⟨false,false,⟨⟨(21019/31993),(166288/95979),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound843 : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩

private abbrev sourceBound856 : CertBound := ⟨false,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private abbrev sourceBound868 : CertBound := ⟨false,false,⟨⟨(16701/5317),(-7898/5317),0,0⟩,⟨(9/26),(1/26),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound870 : CertBound := ⟨false,false,⟨⟨(304094050/73779101),(-85358650/73779101),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound1020 : CertBound := ⟨false,true,⟨⟨(3239071/141278334),(1887079/141278334),0,0⟩,⟨(1307/3191),(1/9573),0,0⟩,⟨(6051/14758),(-1/14758),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1048 : CertBound := ⟨false,true,⟨⟨(1849741/45885169),(3232852/137655507),0,0⟩,⟨(2283/5533),(1/5533),0,0⟩,⟨(3428/8293),(-1/8293),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1065 : CertBound := ⟨false,true,⟨⟨(1482277/29217766),(2590429/87653298),0,0⟩,⟨(2000/4561),(1/4561),0,0⟩,⟨(2815/6406),(-1/6406),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1087 : CertBound := ⟨false,true,⟨⟨(846361/9537054),(493039/9537054),0,0⟩,⟨(1085/2593),(1/2593),0,0⟩,⟨(515/1226),(-1/3678),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1096 : CertBound := ⟨false,true,⟨⟨(268142813350/2731343647201),(5462261750/8194030941603),0,0⟩,⟨(12645/30862),(-1/30862),0,0⟩,⟨(11607/28307),(1/84921),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1113 : CertBound := ⟨false,true,⟨⟨(82907566100/478723971011),(506816000/478723971011),0,0⟩,⟨(7298/17677),(-1/17677),0,0⟩,⟨(19695/47641),(1/47641),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1125 : CertBound := ⟨false,true,⟨⟨(27904867/127104900),(6016573/127104900),0,0⟩,⟨(89/218),(1/654),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1134 : CertBound := ⟨false,true,⟨⟨(348634303500/1397799279019),(-16400787500/1397799279019),0,0⟩,⟨(19695/47641),(1/47641),0,0⟩,⟨(517/1249),(-1/1249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1144 : CertBound := ⟨false,true,⟨⟨(68586194850/178709345581),(991451750/536128036743),0,0⟩,⟨(1137/2714),(-1/8142),0,0⟩,⟨(8849/21061),(1/21061),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1154 : CertBound := ⟨false,true,⟨⟨(151698148500/261719550079),(-11626862500/261719550079),0,0⟩,⟨(8849/21061),(1/21061),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1156 : CertBound := ⟨false,true,⟨⟨(128103/216361),(223856/649083),0,0⟩,⟨(168/409),(1/409),0,0⟩,⟨(223/529),(-1/529),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

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
namespace SourceMemo20_6
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,6,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([1],[]),true)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound807,sourceBound19,sourceBound207,sourceBound699,sourceBound803,sourceBound1065]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : ([sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound807,sourceBound19,sourceBound207,sourceBound699,sourceBound803,sourceBound1065] ++ [sourceBound207]).eraseDups = expected[0] := by
  have hdup : sourceBound207 ∈ expected[0] := by simp [expected]
  change (expected[0] ++ [sourceBound207]).eraseDups = expected[0]
  rw [List.eraseDups_append, erase0,
    BindingSourceSupport20.singleton_removeAll_of_mem hdup,
    List.eraseDups_nil, List.append_nil]
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_6.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b7 := sourceBound7) (b19 := sourceBound19) (b21 := sourceBound21) (b207 := sourceBound207) (b260 := sourceBound260) (b275 := sourceBound275) (b371 := sourceBound371) (b440 := sourceBound440) (b442 := sourceBound442) (b699 := sourceBound699) (b803 := sourceBound803) (b807 := sourceBound807) (b814 := sourceBound814) (b843 := sourceBound843) (b856 := sourceBound856) (b1065 := sourceBound1065)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG0.2.2.1) (BindingSourceBranches20.branchesG1.2.1) (BindingSourceBranches20.branchesG1.2.2.2.1) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm2 BindingNumeric20.norm9 BindingNumeric20.norm11 BindingNumeric20.pullKey22 BindingNumeric20.pullKey23 BindingNumeric20.pullKey24 eraseActual0)
end SourceMemo20_6

open Freiman
open Freiman
namespace SourceMemo20_7
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,7,[1],([2],[3]),false,[(([2],[1]),true)],([1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound277,sourceBound827,sourceBound870,sourceBound1156]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : ([sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound277,sourceBound827,sourceBound870,sourceBound1156] ++ [sourceBound277]).eraseDups = expected[0] := by
  have hdup : sourceBound277 ∈ expected[0] := by simp [expected]
  change (expected[0] ++ [sourceBound277]).eraseDups = expected[0]
  rw [List.eraseDups_append, erase0,
    BindingSourceSupport20.singleton_removeAll_of_mem hdup,
    List.eraseDups_nil, List.append_nil]
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_7.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b21 := sourceBound21) (b260 := sourceBound260) (b275 := sourceBound275) (b277 := sourceBound277) (b371 := sourceBound371) (b440 := sourceBound440) (b442 := sourceBound442) (b827 := sourceBound827) (b843 := sourceBound843) (b856 := sourceBound856) (b870 := sourceBound870) (b1156 := sourceBound1156)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG1.2.2.2.2.1) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm12 BindingNumeric20.pullKey30 BindingNumeric20.pullKey31 BindingNumeric20.pullKey32 eraseActual0)
end SourceMemo20_7

open Freiman
open Freiman
namespace SourceMemo20_8
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,8,[1],([2],[3]),false,[(([2],[1]),false),(([3],[]),true),(([],[1]),false)],([1,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound1125,sourceBound408,sourceBound695,sourceBound1096,sourceBound407,sourceBound675,sourceBound758,sourceBound1020,sourceBound212]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound1125,sourceBound408,sourceBound695,sourceBound1096,sourceBound407,sourceBound675,sourceBound758,sourceBound1020,sourceBound212].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_8.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b5 := sourceBound5) (b21 := sourceBound21) (b212 := sourceBound212) (b260 := sourceBound260) (b275 := sourceBound275) (b371 := sourceBound371) (b407 := sourceBound407) (b408 := sourceBound408) (b440 := sourceBound440) (b442 := sourceBound442) (b675 := sourceBound675) (b695 := sourceBound695) (b758 := sourceBound758) (b817 := sourceBound817) (b843 := sourceBound843) (b856 := sourceBound856) (b1020 := sourceBound1020) (b1096 := sourceBound1096) (b1125 := sourceBound1125)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG1.2.2.2.2.2.1) (BindingSourceBranches20.branchesG1.2.2.2.2.2.2.1) (BindingSourceBranches20.branchesG1.2.2.2.2.2.2.2) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm13 BindingNumeric20.pull36 BindingNumeric20.norm14 BindingNumeric20.pullKey34 BindingNumeric20.norm15 BindingNumeric20.pullKey35 BindingNumeric20.pullKey36 BindingNumeric20.pullKey37 eraseActual0)
end SourceMemo20_8

open Freiman
open Freiman
namespace SourceMemo20_9
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,9,[1],([2],[3]),false,[(([2],[1]),false),(([2],[]),true),(([],[1]),false)],([1,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound1125,sourceBound411,sourceBound734,sourceBound1113,sourceBound402,sourceBound693,sourceBound787,sourceBound1048,sourceBound205],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound1125,sourceBound411,sourceBound734,sourceBound243,sourceBound775,sourceBound704,sourceBound1134,sourceBound402,sourceBound693,sourceBound787,sourceBound1048,sourceBound205],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound250,sourceBound868,sourceBound411,sourceBound734,sourceBound1113,sourceBound402,sourceBound693,sourceBound787,sourceBound1048,sourceBound205],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound250,sourceBound868,sourceBound411,sourceBound734,sourceBound243,sourceBound775,sourceBound704,sourceBound1134,sourceBound402,sourceBound693,sourceBound787,sourceBound1048,sourceBound205]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound1125,sourceBound411,sourceBound734,sourceBound1113,sourceBound402,sourceBound693,sourceBound787,sourceBound1048,sourceBound205].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound1125,sourceBound411,sourceBound734,sourceBound243,sourceBound775,sourceBound704,sourceBound1134,sourceBound402,sourceBound693,sourceBound787,sourceBound1048,sourceBound205].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem erase2 : expected[2].eraseDups = expected[2] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[2] (by simp [expected])))
private theorem eraseActual2 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound250,sourceBound868,sourceBound411,sourceBound734,sourceBound1113,sourceBound402,sourceBound693,sourceBound787,sourceBound1048,sourceBound205].eraseDups = expected[2] := by
  simpa [expected] using erase2
private theorem erase3 : expected[3].eraseDups = expected[3] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[3] (by simp [expected])))
private theorem eraseActual3 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound250,sourceBound868,sourceBound411,sourceBound734,sourceBound243,sourceBound775,sourceBound704,sourceBound1134,sourceBound402,sourceBound693,sourceBound787,sourceBound1048,sourceBound205].eraseDups = expected[3] := by
  simpa [expected] using erase3
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_9.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b5 := sourceBound5) (b21 := sourceBound21) (b205 := sourceBound205) (b243 := sourceBound243) (b250 := sourceBound250) (b260 := sourceBound260) (b275 := sourceBound275) (b371 := sourceBound371) (b402 := sourceBound402) (b411 := sourceBound411) (b440 := sourceBound440) (b442 := sourceBound442) (b693 := sourceBound693) (b704 := sourceBound704) (b734 := sourceBound734) (b775 := sourceBound775) (b787 := sourceBound787) (b817 := sourceBound817) (b843 := sourceBound843) (b856 := sourceBound856) (b868 := sourceBound868) (b1048 := sourceBound1048) (b1113 := sourceBound1113) (b1125 := sourceBound1125) (b1134 := sourceBound1134)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG1.2.2.2.2.2.1) (BindingSourceBranches20.branchesG2.1) (BindingSourceBranches20.branchesG2.2.1) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm13 BindingNumeric20.pull36 BindingNumeric20.pullKey33 BindingNumeric20.pullKey38 BindingNumeric20.norm16 BindingNumeric20.pullKey39 BindingNumeric20.pull44 BindingNumeric20.pullKey40 BindingNumeric20.pullKey41 BindingNumeric20.pullKey42 BindingNumeric20.norm17 BindingNumeric20.pullKey43 BindingNumeric20.pullKey44 BindingNumeric20.pullKey45 eraseActual0 eraseActual1 eraseActual2 eraseActual3)
end SourceMemo20_9

open Freiman
open Freiman
namespace SourceMemo20_10
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,10,[1],([2],[3]),false,[(([2],[1]),false),(([1],[]),true),(([],[1]),false)],([1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound256,sourceBound801,sourceBound1144,sourceBound409,sourceBound738,sourceBound823,sourceBound1087,sourceBound224],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound256,sourceBound801,sourceBound265,sourceBound815,sourceBound768,sourceBound1154,sourceBound409,sourceBound738,sourceBound823,sourceBound1087,sourceBound224]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound256,sourceBound801,sourceBound1144,sourceBound409,sourceBound738,sourceBound823,sourceBound1087,sourceBound224].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound817,sourceBound5,sourceBound256,sourceBound801,sourceBound265,sourceBound815,sourceBound768,sourceBound1154,sourceBound409,sourceBound738,sourceBound823,sourceBound1087,sourceBound224].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_10.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b5 := sourceBound5) (b21 := sourceBound21) (b224 := sourceBound224) (b256 := sourceBound256) (b260 := sourceBound260) (b265 := sourceBound265) (b275 := sourceBound275) (b371 := sourceBound371) (b409 := sourceBound409) (b440 := sourceBound440) (b442 := sourceBound442) (b738 := sourceBound738) (b768 := sourceBound768) (b801 := sourceBound801) (b815 := sourceBound815) (b817 := sourceBound817) (b823 := sourceBound823) (b843 := sourceBound843) (b856 := sourceBound856) (b1087 := sourceBound1087) (b1144 := sourceBound1144) (b1154 := sourceBound1154)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG1.2.2.2.2.2.1) (BindingSourceBranches20.branchesG2.2.2.1) (BindingSourceBranches20.branchesG2.2.2.2.1) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm13 BindingNumeric20.norm18 BindingNumeric20.pullKey46 BindingNumeric20.pull52 BindingNumeric20.pullKey47 BindingNumeric20.pullKey48 BindingNumeric20.pullKey49 BindingNumeric20.norm19 BindingNumeric20.pullKey50 BindingNumeric20.pullKey51 BindingNumeric20.pullKey52 eraseActual0 eraseActual1)
end SourceMemo20_10

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
namespace BatchLookup20
set_option maxRecDepth 30000
set_option maxHeartbeats 0
private theorem nonleft_catalogs :
  (∀ r ∈ lowerHistoryRecordsR.toList, r.catalog ≠ .left) ∧
  (∀ r ∈ lowerHistoryRecordsM.toList, r.catalog ≠ .left) ∧
  (∀ r ∈ lowerHistoryRecordsX.toList, r.catalog ≠ .left) ∧
  (∀ r ∈ lowerHistoryRecordsH.toList, r.catalog ≠ .left) := by
  decide +kernel
private theorem lowerHistoryRecordsL_list : lowerHistoryRecordsL.toList = ([
  ⟨.left,1,0,(-1),false,494,1186⟩,
  ⟨.left,2,0,(-1),false,221,1132⟩,
  ⟨.left,3,0,(-1),false,219,1138⟩,
  ⟨.left,3,1,(-1),false,215,1138⟩,
  ⟨.left,3,2,(-1),false,217,1138⟩,
  ⟨.left,3,3,(-1),false,213,1138⟩,
  ⟨.left,4,0,(-1),false,227,1174⟩,
  ⟨.left,4,1,(-1),false,225,1174⟩,
  ⟨.left,5,0,(-1),false,207,1156⟩,
  ⟨.left,6,0,(-1),false,209,1174⟩,
  ⟨.left,7,0,(-1),false,511,1192⟩,
  ⟨.left,8,0,(-1),false,117,1144⟩,
  ⟨.left,9,0,(-1),false,114,1162⟩,
  ⟨.left,9,1,(-1),false,108,1162⟩,
  ⟨.left,9,2,(-1),false,111,1162⟩,
  ⟨.left,9,3,(-1),false,105,1162⟩,
  ⟨.left,10,0,(-1),false,126,1180⟩,
  ⟨.left,10,1,(-1),false,123,1180⟩,
  ⟨.left,11,0,(-1),false,99,1150⟩,
  ⟨.left,12,0,(-1),false,93,1168⟩,
  ⟨.left,13,0,(-1),false,96,1180⟩,
  ⟨.left,14,0,(-1),false,345,937⟩,
  ⟨.left,15,0,(-1),false,346,973⟩,
  ⟨.left,16,0,(-1),false,339,817⟩,
  ⟨.left,17,0,(-1),false,336,823⟩,
  ⟨.left,17,1,(-1),false,334,823⟩,
  ⟨.left,17,2,(-1),false,335,823⟩,
  ⟨.left,17,3,(-1),false,333,823⟩,
  ⟨.left,18,0,(-1),false,338,859⟩,
  ⟨.left,18,1,(-1),false,337,859⟩,
  ⟨.left,19,0,(-1),false,422,973⟩,
  ⟨.left,19,1,(-1),false,421,973⟩,
  ⟨.left,20,0,(-1),false,222,883⟩,
  ⟨.left,21,0,(-1),false,220,913⟩,
  ⟨.left,21,1,(-1),false,216,913⟩,
  ⟨.left,21,2,(-1),false,218,913⟩,
  ⟨.left,21,3,(-1),false,214,913⟩,
  ⟨.left,22,0,(-1),false,228,973⟩,
  ⟨.left,22,1,(-1),false,226,973⟩,
  ⟨.left,23,0,(-1),false,208,937⟩,
  ⟨.left,24,0,(-1),false,210,973⟩,
  ⟨.left,25,0,(-1),false,512,1024⟩,
  ⟨.left,26,0,(-1),false,296,931⟩,
  ⟨.left,26,1,(-1),false,294,931⟩,
  ⟨.left,26,2,(-1),false,295,931⟩,
  ⟨.left,26,3,(-1),false,293,931⟩,
  ⟨.left,27,0,(-1),false,288,961⟩,
  ⟨.left,27,1,(-1),false,286,961⟩,
  ⟨.left,27,2,(-1),false,287,961⟩,
  ⟨.left,27,3,(-1),false,285,961⟩,
  ⟨.left,28,0,(-1),false,292,991⟩,
  ⟨.left,28,1,(-1),false,290,991⟩,
  ⟨.left,28,2,(-1),false,291,991⟩,
  ⟨.left,28,3,(-1),false,289,991⟩,
  ⟨.left,29,0,(-1),false,264,829⟩,
  ⟨.left,29,1,(-1),false,262,829⟩,
  ⟨.left,29,2,(-1),false,263,829⟩,
  ⟨.left,29,3,(-1),false,261,829⟩,
  ⟨.left,30,0,(-1),false,252,847⟩,
  ⟨.left,30,1,(-1),false,244,847⟩,
  ⟨.left,30,2,(-1),false,248,847⟩,
  ⟨.left,30,3,(-1),false,240,847⟩,
  ⟨.left,30,4,(-1),false,250,847⟩,
  ⟨.left,30,5,(-1),false,242,847⟩,
  ⟨.left,30,6,(-1),false,246,847⟩,
  ⟨.left,30,7,(-1),false,238,847⟩,
  ⟨.left,30,8,(-1),false,251,847⟩,
  ⟨.left,30,9,(-1),false,243,847⟩,
  ⟨.left,30,10,(-1),false,247,847⟩,
  ⟨.left,30,11,(-1),false,239,847⟩,
  ⟨.left,30,12,(-1),false,249,847⟩,
  ⟨.left,30,13,(-1),false,241,847⟩,
  ⟨.left,30,14,(-1),false,245,847⟩,
  ⟨.left,30,15,(-1),false,237,847⟩,
  ⟨.left,31,0,(-1),false,260,889⟩,
  ⟨.left,31,1,(-1),false,256,889⟩,
  ⟨.left,31,2,(-1),false,258,889⟩,
  ⟨.left,31,3,(-1),false,254,889⟩,
  ⟨.left,31,4,(-1),false,259,889⟩,
  ⟨.left,31,5,(-1),false,255,889⟩,
  ⟨.left,31,6,(-1),false,257,889⟩,
  ⟨.left,31,7,(-1),false,253,889⟩,
  ⟨.left,32,0,(-1),false,430,991⟩,
  ⟨.left,32,1,(-1),false,426,991⟩,
  ⟨.left,32,2,(-1),false,428,991⟩,
  ⟨.left,32,3,(-1),false,424,991⟩,
  ⟨.left,32,4,(-1),false,429,991⟩,
  ⟨.left,32,5,(-1),false,425,991⟩,
  ⟨.left,32,6,(-1),false,427,991⟩,
  ⟨.left,32,7,(-1),false,423,991⟩,
  ⟨.left,33,0,(-1),false,118,925⟩,
  ⟨.left,33,1,(-1),false,116,925⟩,
  ⟨.left,34,0,(-1),false,115,955⟩,
  ⟨.left,34,1,(-1),false,109,955⟩,
  ⟨.left,34,2,(-1),false,112,955⟩,
  ⟨.left,34,3,(-1),false,106,955⟩,
  ⟨.left,34,4,(-1),false,113,955⟩,
  ⟨.left,34,5,(-1),false,107,955⟩,
  ⟨.left,34,6,(-1),false,110,955⟩,
  ⟨.left,34,7,(-1),false,104,955⟩,
  ⟨.left,35,0,(-1),false,127,991⟩,
  ⟨.left,35,1,(-1),false,124,991⟩,
  ⟨.left,35,2,(-1),false,125,991⟩,
  ⟨.left,35,3,(-1),false,122,991⟩,
  ⟨.left,36,0,(-1),false,100,931⟩,
  ⟨.left,36,1,(-1),false,98,931⟩,
  ⟨.left,37,0,(-1),false,94,961⟩,
  ⟨.left,37,1,(-1),false,92,961⟩,
  ⟨.left,38,0,(-1),false,97,991⟩,
  ⟨.left,38,1,(-1),false,95,991⟩,
  ⟨.left,39,0,(-1),false,513,1048⟩,
  ⟨.left,39,1,0,false,509,1020⟩,
  ⟨.left,39,1,1,false,503,50⟩,
  ⟨.left,39,1,2,false,505,580⟩,
  ⟨.left,39,1,3,false,507,280⟩,
  ⟨.left,39,1,4,false,453,794⟩,
  ⟨.left,39,1,5,false,450,36⟩,
  ⟨.left,39,1,6,false,451,566⟩,
  ⟨.left,39,1,7,false,452,266⟩,
  ⟨.left,39,1,8,false,501,306⟩,
  ⟨.left,39,1,9,false,495,40⟩,
  ⟨.left,39,1,10,false,497,570⟩,
  ⟨.left,39,1,11,false,498,270⟩,
  ⟨.left,39,1,12,false,502,799⟩,
  ⟨.left,39,1,13,false,496,44⟩,
  ⟨.left,39,1,14,false,499,574⟩,
  ⟨.left,39,1,15,false,500,274⟩,
  ⟨.left,40,0,(-1),false,202,967⟩,
  ⟨.left,40,1,(-1),false,201,137⟩,
  ⟨.left,41,0,(-1),false,200,985⟩,
  ⟨.left,41,1,(-1),false,199,143⟩,
  ⟨.left,42,0,(-1),false,204,1005⟩,
  ⟨.left,42,1,(-1),false,203,149⟩,
  ⟨.left,43,0,(-1),false,190,871⟩,
  ⟨.left,43,1,(-1),false,189,119⟩,
  ⟨.left,44,0,(-1),false,178,901⟩,
  ⟨.left,44,1,(-1),false,174,901⟩,
  ⟨.left,44,2,(-1),false,176,901⟩,
  ⟨.left,44,3,(-1),false,172,901⟩,
  ⟨.left,44,4,(-1),false,177,125⟩,
  ⟨.left,44,5,(-1),false,173,125⟩,
  ⟨.left,44,6,(-1),false,175,125⟩,
  ⟨.left,44,7,(-1),false,171,125⟩,
  ⟨.left,45,0,(-1),false,182,943⟩,
  ⟨.left,45,1,(-1),false,180,943⟩,
  ⟨.left,45,2,(-1),false,181,131⟩,
  ⟨.left,45,3,(-1),false,179,131⟩,
  ⟨.left,46,0,(-1),false,434,1005⟩,
  ⟨.left,46,1,(-1),false,432,66⟩,
  ⟨.left,46,2,(-1),false,433,149⟩,
  ⟨.left,46,3,(-1),false,431,149⟩,
  ⟨.left,47,0,(-1),false,55,979⟩,
  ⟨.left,48,0,(-1),false,40,997⟩,
  ⟨.left,48,1,(-1),false,38,997⟩,
  ⟨.left,48,2,(-1),false,39,997⟩,
  ⟨.left,48,3,(-1),false,37,997⟩,
  ⟨.left,49,0,(-1),false,42,1005⟩,
  ⟨.left,49,1,(-1),false,41,66⟩,
  ⟨.left,50,0,(-1),false,22,967⟩,
  ⟨.left,51,0,(-1),false,21,985⟩,
  ⟨.left,52,0,(-1),false,23,1005⟩,
  ⟨.left,53,0,(-1),false,514,197⟩,
  ⟨.left,54,0,(-1),false,418,979⟩,
  ⟨.left,54,1,(-1),false,411,979⟩,
  ⟨.left,54,2,(-1),false,419,979⟩,
  ⟨.left,55,0,(-1),false,389,877⟩,
  ⟨.left,55,1,(-1),false,388,877⟩,
  ⟨.left,55,2,(-1),false,390,877⟩,
  ⟨.left,56,0,(-1),false,393,919⟩,
  ⟨.left,56,1,(-1),false,392,919⟩,
  ⟨.left,56,2,(-1),false,394,919⟩,
  ⟨.left,57,0,(-1),false,401,979⟩,
  ⟨.left,57,1,(-1),false,400,979⟩,
  ⟨.left,57,2,(-1),false,402,979⟩,
  ⟨.left,58,0,(-1),false,361,835⟩,
  ⟨.left,58,1,(-1),false,353,835⟩,
  ⟨.left,58,2,(-1),false,357,835⟩,
  ⟨.left,58,3,(-1),false,349,835⟩,
  ⟨.left,58,4,(-1),false,360,835⟩,
  ⟨.left,58,5,(-1),false,352,835⟩,
  ⟨.left,58,6,(-1),false,356,835⟩,
  ⟨.left,58,7,(-1),false,348,835⟩,
  ⟨.left,58,8,(-1),false,362,835⟩,
  ⟨.left,58,9,(-1),false,354,835⟩,
  ⟨.left,58,10,(-1),false,358,835⟩,
  ⟨.left,58,11,(-1),false,350,835⟩,
  ⟨.left,59,0,(-1),false,369,865⟩,
  ⟨.left,59,1,(-1),false,365,865⟩,
  ⟨.left,59,2,(-1),false,368,865⟩,
  ⟨.left,59,3,(-1),false,364,865⟩,
  ⟨.left,59,4,(-1),false,370,865⟩,
  ⟨.left,59,5,(-1),false,366,865⟩,
  ⟨.left,60,0,(-1),false,406,997⟩,
  ⟨.left,60,1,(-1),false,404,997⟩,
  ⟨.left,61,0,(-1),false,325,907⟩,
  ⟨.left,62,0,(-1),false,327,949⟩,
  ⟨.left,63,0,(-1),false,329,997⟩,
  ⟨.left,64,0,(-1),false,323,841⟩,
  ⟨.left,65,0,(-1),false,307,853⟩,
  ⟨.left,65,1,(-1),false,303,853⟩,
  ⟨.left,65,2,(-1),false,305,853⟩,
  ⟨.left,65,3,(-1),false,301,853⟩,
  ⟨.left,66,0,(-1),false,311,895⟩,
  ⟨.left,66,1,(-1),false,309,895⟩,
  ⟨.left,67,0,(-1),false,34,979⟩,
  ⟨.left,68,0,(-1),false,28,997⟩,
  ⟨.left,68,1,(-1),false,26,997⟩,
  ⟨.left,68,2,(-1),false,27,997⟩,
  ⟨.left,68,3,(-1),false,25,997⟩,
  ⟨.left,69,0,(-1),false,30,1005⟩,
  ⟨.left,69,1,(-1),false,29,66⟩,
  ⟨.left,70,0,(-1),false,18,967⟩,
  ⟨.left,71,0,(-1),false,17,985⟩,
  ⟨.left,72,0,(-1),false,19,1005⟩,
  ⟨.left,73,0,(-1),false,391,877⟩,
  ⟨.left,74,0,(-1),false,395,919⟩,
  ⟨.left,75,0,(-1),false,403,979⟩,
  ⟨.left,76,0,(-1),false,363,835⟩,
  ⟨.left,76,1,(-1),false,355,835⟩,
  ⟨.left,76,2,(-1),false,359,835⟩,
  ⟨.left,76,3,(-1),false,351,835⟩,
  ⟨.left,77,0,(-1),false,371,865⟩,
  ⟨.left,77,1,(-1),false,367,865⟩,
  ⟨.left,78,0,(-1),false,420,979⟩,
  ⟨.left,79,0,(-1),false,326,907⟩,
  ⟨.left,80,0,(-1),false,328,949⟩,
  ⟨.left,81,0,(-1),false,330,997⟩,
  ⟨.left,82,0,(-1),false,324,841⟩,
  ⟨.left,83,0,(-1),false,308,853⟩,
  ⟨.left,83,1,(-1),false,304,853⟩,
  ⟨.left,83,2,(-1),false,306,853⟩,
  ⟨.left,83,3,(-1),false,302,853⟩,
  ⟨.left,84,0,(-1),false,312,895⟩,
  ⟨.left,84,1,(-1),false,310,895⟩,
  ⟨.left,85,0,(-1),false,407,997⟩,
  ⟨.left,85,1,(-1),false,405,997⟩,
  ⟨.left,86,0,(-1),false,196,967⟩,
  ⟨.left,87,0,(-1),false,195,985⟩,
  ⟨.left,88,0,(-1),false,197,1005⟩,
  ⟨.left,89,0,(-1),false,168,871⟩,
  ⟨.left,90,0,(-1),false,162,901⟩,
  ⟨.left,90,1,(-1),false,160,901⟩,
  ⟨.left,90,2,(-1),false,161,901⟩,
  ⟨.left,90,3,(-1),false,159,901⟩,
  ⟨.left,91,0,(-1),false,164,943⟩,
  ⟨.left,91,1,(-1),false,163,943⟩,
  ⟨.left,92,0,(-1),false,409,1005⟩,
  ⟨.left,92,1,(-1),false,408,66⟩,
  ⟨.left,93,0,(-1),false,13,243⟩,
  ⟨.left,94,0,(-1),false,14,215⟩,
  ⟨.left,95,0,(-1),false,15,215⟩,
  ⟨.left,96,0,(-1),false,10,225⟩,
  ⟨.left,97,0,(-1),false,4,231⟩,
  ⟨.left,97,1,(-1),false,2,231⟩,
  ⟨.left,97,2,(-1),false,3,231⟩,
  ⟨.left,97,3,(-1),false,1,231⟩,
  ⟨.left,98,0,(-1),false,6,237⟩,
  ⟨.left,98,1,(-1),false,5,237⟩,
  ⟨.left,99,0,(-1),false,516,290⟩,
  ⟨.left,99,1,(-1),false,515,296⟩,
  ⟨.left,100,0,(-1),false,494,1185⟩,
  ⟨.left,101,0,(-1),false,221,1131⟩,
  ⟨.left,102,0,(-1),false,219,1137⟩,
  ⟨.left,102,1,(-1),false,215,1137⟩,
  ⟨.left,102,2,(-1),false,217,1137⟩,
  ⟨.left,102,3,(-1),false,213,1137⟩,
  ⟨.left,103,0,(-1),false,227,1173⟩,
  ⟨.left,103,1,(-1),false,225,1173⟩,
  ⟨.left,104,0,(-1),false,207,1155⟩,
  ⟨.left,105,0,(-1),false,209,1173⟩,
  ⟨.left,106,0,(-1),false,511,1191⟩,
  ⟨.left,107,0,(-1),false,117,1143⟩,
  ⟨.left,108,0,(-1),false,114,1161⟩,
  ⟨.left,108,1,(-1),false,108,1161⟩,
  ⟨.left,108,2,(-1),false,111,1161⟩,
  ⟨.left,108,3,(-1),false,105,1161⟩,
  ⟨.left,109,0,(-1),false,126,1179⟩,
  ⟨.left,109,1,(-1),false,123,1179⟩,
  ⟨.left,110,0,(-1),false,99,1149⟩,
  ⟨.left,111,0,(-1),false,93,1167⟩,
  ⟨.left,112,0,(-1),false,96,1179⟩,
  ⟨.left,113,0,(-1),false,345,936⟩,
  ⟨.left,114,0,(-1),false,346,972⟩,
  ⟨.left,115,0,(-1),false,339,816⟩,
  ⟨.left,116,0,(-1),false,336,822⟩,
  ⟨.left,116,1,(-1),false,334,822⟩,
  ⟨.left,116,2,(-1),false,335,822⟩,
  ⟨.left,116,3,(-1),false,333,822⟩,
  ⟨.left,117,0,(-1),false,338,858⟩,
  ⟨.left,117,1,(-1),false,337,858⟩,
  ⟨.left,118,0,(-1),false,422,972⟩,
  ⟨.left,118,1,(-1),false,421,972⟩,
  ⟨.left,119,0,(-1),false,222,882⟩,
  ⟨.left,120,0,(-1),false,220,912⟩,
  ⟨.left,120,1,(-1),false,216,912⟩,
  ⟨.left,120,2,(-1),false,218,912⟩,
  ⟨.left,120,3,(-1),false,214,912⟩,
  ⟨.left,121,0,(-1),false,228,972⟩,
  ⟨.left,121,1,(-1),false,226,972⟩,
  ⟨.left,122,0,(-1),false,208,936⟩,
  ⟨.left,123,0,(-1),false,210,972⟩,
  ⟨.left,124,0,(-1),false,512,1023⟩,
  ⟨.left,125,0,(-1),false,296,930⟩,
  ⟨.left,125,1,(-1),false,294,930⟩,
  ⟨.left,125,2,(-1),false,295,930⟩,
  ⟨.left,125,3,(-1),false,293,930⟩,
  ⟨.left,126,0,(-1),false,288,960⟩,
  ⟨.left,126,1,(-1),false,286,960⟩,
  ⟨.left,126,2,(-1),false,287,960⟩,
  ⟨.left,126,3,(-1),false,285,960⟩,
  ⟨.left,127,0,(-1),false,292,990⟩,
  ⟨.left,127,1,(-1),false,290,990⟩,
  ⟨.left,127,2,(-1),false,291,990⟩,
  ⟨.left,127,3,(-1),false,289,990⟩,
  ⟨.left,128,0,(-1),false,264,828⟩,
  ⟨.left,128,1,(-1),false,262,828⟩,
  ⟨.left,128,2,(-1),false,263,828⟩,
  ⟨.left,128,3,(-1),false,261,828⟩,
  ⟨.left,129,0,(-1),false,252,846⟩,
  ⟨.left,129,1,(-1),false,244,846⟩,
  ⟨.left,129,2,(-1),false,248,846⟩,
  ⟨.left,129,3,(-1),false,240,846⟩,
  ⟨.left,129,4,(-1),false,250,846⟩,
  ⟨.left,129,5,(-1),false,242,846⟩,
  ⟨.left,129,6,(-1),false,246,846⟩,
  ⟨.left,129,7,(-1),false,238,846⟩,
  ⟨.left,129,8,(-1),false,251,846⟩,
  ⟨.left,129,9,(-1),false,243,846⟩,
  ⟨.left,129,10,(-1),false,247,846⟩,
  ⟨.left,129,11,(-1),false,239,846⟩,
  ⟨.left,129,12,(-1),false,249,846⟩,
  ⟨.left,129,13,(-1),false,241,846⟩,
  ⟨.left,129,14,(-1),false,245,846⟩,
  ⟨.left,129,15,(-1),false,237,846⟩,
  ⟨.left,130,0,(-1),false,260,888⟩,
  ⟨.left,130,1,(-1),false,256,888⟩,
  ⟨.left,130,2,(-1),false,258,888⟩,
  ⟨.left,130,3,(-1),false,254,888⟩,
  ⟨.left,130,4,(-1),false,259,888⟩,
  ⟨.left,130,5,(-1),false,255,888⟩,
  ⟨.left,130,6,(-1),false,257,888⟩,
  ⟨.left,130,7,(-1),false,253,888⟩,
  ⟨.left,131,0,(-1),false,430,990⟩,
  ⟨.left,131,1,(-1),false,426,990⟩,
  ⟨.left,131,2,(-1),false,428,990⟩,
  ⟨.left,131,3,(-1),false,424,990⟩,
  ⟨.left,131,4,(-1),false,429,990⟩,
  ⟨.left,131,5,(-1),false,425,990⟩,
  ⟨.left,131,6,(-1),false,427,990⟩,
  ⟨.left,131,7,(-1),false,423,990⟩,
  ⟨.left,132,0,(-1),false,118,924⟩,
  ⟨.left,132,1,(-1),false,116,924⟩,
  ⟨.left,133,0,(-1),false,115,954⟩,
  ⟨.left,133,1,(-1),false,109,954⟩,
  ⟨.left,133,2,(-1),false,112,954⟩,
  ⟨.left,133,3,(-1),false,106,954⟩,
  ⟨.left,133,4,(-1),false,113,954⟩,
  ⟨.left,133,5,(-1),false,107,954⟩,
  ⟨.left,133,6,(-1),false,110,954⟩,
  ⟨.left,133,7,(-1),false,104,954⟩,
  ⟨.left,134,0,(-1),false,127,990⟩,
  ⟨.left,134,1,(-1),false,124,990⟩,
  ⟨.left,134,2,(-1),false,125,990⟩,
  ⟨.left,134,3,(-1),false,122,990⟩,
  ⟨.left,135,0,(-1),false,100,930⟩,
  ⟨.left,135,1,(-1),false,98,930⟩,
  ⟨.left,136,0,(-1),false,94,960⟩,
  ⟨.left,136,1,(-1),false,92,960⟩,
  ⟨.left,137,0,(-1),false,97,990⟩,
  ⟨.left,137,1,(-1),false,95,990⟩,
  ⟨.left,138,0,(-1),false,513,13⟩,
  ⟨.left,138,1,0,false,509,10⟩,
  ⟨.left,138,1,1,false,503,49⟩,
  ⟨.left,138,1,2,false,505,579⟩,
  ⟨.left,138,1,3,false,507,279⟩,
  ⟨.left,138,1,4,false,453,3⟩,
  ⟨.left,138,1,5,false,450,35⟩,
  ⟨.left,138,1,6,false,451,565⟩,
  ⟨.left,138,1,7,false,452,265⟩,
  ⟨.left,138,1,8,false,501,305⟩,
  ⟨.left,138,1,9,false,495,39⟩,
  ⟨.left,138,1,10,false,497,569⟩,
  ⟨.left,138,1,11,false,498,269⟩,
  ⟨.left,138,1,12,false,502,6⟩,
  ⟨.left,138,1,13,false,496,43⟩,
  ⟨.left,138,1,14,false,499,573⟩,
  ⟨.left,138,1,15,false,500,273⟩,
  ⟨.left,139,0,(-1),false,202,966⟩,
  ⟨.left,139,1,(-1),false,201,136⟩,
  ⟨.left,140,0,(-1),false,200,984⟩,
  ⟨.left,140,1,(-1),false,199,142⟩,
  ⟨.left,141,0,(-1),false,204,1004⟩,
  ⟨.left,141,1,(-1),false,203,148⟩,
  ⟨.left,142,0,(-1),false,190,870⟩,
  ⟨.left,142,1,(-1),false,189,118⟩,
  ⟨.left,143,0,(-1),false,178,900⟩,
  ⟨.left,143,1,(-1),false,174,900⟩,
  ⟨.left,143,2,(-1),false,176,900⟩,
  ⟨.left,143,3,(-1),false,172,900⟩,
  ⟨.left,143,4,(-1),false,177,124⟩,
  ⟨.left,143,5,(-1),false,173,124⟩,
  ⟨.left,143,6,(-1),false,175,124⟩,
  ⟨.left,143,7,(-1),false,171,124⟩,
  ⟨.left,144,0,(-1),false,182,942⟩,
  ⟨.left,144,1,(-1),false,180,942⟩,
  ⟨.left,144,2,(-1),false,181,130⟩,
  ⟨.left,144,3,(-1),false,179,130⟩,
  ⟨.left,145,0,(-1),false,434,1004⟩,
  ⟨.left,145,1,(-1),false,432,65⟩,
  ⟨.left,145,2,(-1),false,433,148⟩,
  ⟨.left,145,3,(-1),false,431,148⟩,
  ⟨.left,146,0,(-1),false,55,978⟩,
  ⟨.left,147,0,(-1),false,40,996⟩,
  ⟨.left,147,1,(-1),false,38,996⟩,
  ⟨.left,147,2,(-1),false,39,996⟩,
  ⟨.left,147,3,(-1),false,37,996⟩,
  ⟨.left,148,0,(-1),false,42,1004⟩,
  ⟨.left,148,1,(-1),false,41,65⟩,
  ⟨.left,149,0,(-1),false,22,966⟩,
  ⟨.left,150,0,(-1),false,21,984⟩,
  ⟨.left,151,0,(-1),false,23,1004⟩,
  ⟨.left,152,0,(-1),false,514,196⟩,
  ⟨.left,153,0,(-1),false,418,978⟩,
  ⟨.left,153,1,(-1),false,411,978⟩,
  ⟨.left,153,2,(-1),false,419,978⟩,
  ⟨.left,154,0,(-1),false,389,876⟩,
  ⟨.left,154,1,(-1),false,388,876⟩,
  ⟨.left,154,2,(-1),false,390,876⟩,
  ⟨.left,155,0,(-1),false,393,918⟩,
  ⟨.left,155,1,(-1),false,392,918⟩,
  ⟨.left,155,2,(-1),false,394,918⟩,
  ⟨.left,156,0,(-1),false,401,978⟩,
  ⟨.left,156,1,(-1),false,400,978⟩,
  ⟨.left,156,2,(-1),false,402,978⟩,
  ⟨.left,157,0,(-1),false,361,834⟩,
  ⟨.left,157,1,(-1),false,353,834⟩,
  ⟨.left,157,2,(-1),false,357,834⟩,
  ⟨.left,157,3,(-1),false,349,834⟩,
  ⟨.left,157,4,(-1),false,360,834⟩,
  ⟨.left,157,5,(-1),false,352,834⟩,
  ⟨.left,157,6,(-1),false,356,834⟩,
  ⟨.left,157,7,(-1),false,348,834⟩,
  ⟨.left,157,8,(-1),false,362,834⟩,
  ⟨.left,157,9,(-1),false,354,834⟩,
  ⟨.left,157,10,(-1),false,358,834⟩,
  ⟨.left,157,11,(-1),false,350,834⟩,
  ⟨.left,158,0,(-1),false,369,864⟩,
  ⟨.left,158,1,(-1),false,365,864⟩,
  ⟨.left,158,2,(-1),false,368,864⟩,
  ⟨.left,158,3,(-1),false,364,864⟩,
  ⟨.left,158,4,(-1),false,370,864⟩,
  ⟨.left,158,5,(-1),false,366,864⟩,
  ⟨.left,159,0,(-1),false,406,996⟩,
  ⟨.left,159,1,(-1),false,404,996⟩,
  ⟨.left,160,0,(-1),false,325,906⟩,
  ⟨.left,161,0,(-1),false,327,948⟩,
  ⟨.left,162,0,(-1),false,329,996⟩,
  ⟨.left,163,0,(-1),false,323,840⟩,
  ⟨.left,164,0,(-1),false,307,852⟩,
  ⟨.left,164,1,(-1),false,303,852⟩,
  ⟨.left,164,2,(-1),false,305,852⟩,
  ⟨.left,164,3,(-1),false,301,852⟩,
  ⟨.left,165,0,(-1),false,311,894⟩,
  ⟨.left,165,1,(-1),false,309,894⟩,
  ⟨.left,166,0,(-1),false,34,978⟩,
  ⟨.left,167,0,(-1),false,28,996⟩,
  ⟨.left,167,1,(-1),false,26,996⟩,
  ⟨.left,167,2,(-1),false,27,996⟩,
  ⟨.left,167,3,(-1),false,25,996⟩,
  ⟨.left,168,0,(-1),false,30,1004⟩,
  ⟨.left,168,1,(-1),false,29,65⟩,
  ⟨.left,169,0,(-1),false,18,966⟩,
  ⟨.left,170,0,(-1),false,17,984⟩,
  ⟨.left,171,0,(-1),false,19,1004⟩,
  ⟨.left,172,0,(-1),false,391,876⟩,
  ⟨.left,173,0,(-1),false,395,918⟩,
  ⟨.left,174,0,(-1),false,403,978⟩,
  ⟨.left,175,0,(-1),false,363,834⟩,
  ⟨.left,175,1,(-1),false,355,834⟩,
  ⟨.left,175,2,(-1),false,359,834⟩,
  ⟨.left,175,3,(-1),false,351,834⟩,
  ⟨.left,176,0,(-1),false,371,864⟩,
  ⟨.left,176,1,(-1),false,367,864⟩,
  ⟨.left,177,0,(-1),false,420,978⟩,
  ⟨.left,178,0,(-1),false,326,906⟩,
  ⟨.left,179,0,(-1),false,328,948⟩,
  ⟨.left,180,0,(-1),false,330,996⟩,
  ⟨.left,181,0,(-1),false,324,840⟩,
  ⟨.left,182,0,(-1),false,308,852⟩,
  ⟨.left,182,1,(-1),false,304,852⟩,
  ⟨.left,182,2,(-1),false,306,852⟩,
  ⟨.left,182,3,(-1),false,302,852⟩,
  ⟨.left,183,0,(-1),false,312,894⟩,
  ⟨.left,183,1,(-1),false,310,894⟩,
  ⟨.left,184,0,(-1),false,407,996⟩,
  ⟨.left,184,1,(-1),false,405,996⟩,
  ⟨.left,185,0,(-1),false,196,966⟩,
  ⟨.left,186,0,(-1),false,195,984⟩,
  ⟨.left,187,0,(-1),false,197,1004⟩,
  ⟨.left,188,0,(-1),false,168,870⟩,
  ⟨.left,189,0,(-1),false,162,900⟩,
  ⟨.left,189,1,(-1),false,160,900⟩,
  ⟨.left,189,2,(-1),false,161,900⟩,
  ⟨.left,189,3,(-1),false,159,900⟩,
  ⟨.left,190,0,(-1),false,164,942⟩,
  ⟨.left,190,1,(-1),false,163,942⟩,
  ⟨.left,191,0,(-1),false,409,1004⟩,
  ⟨.left,191,1,(-1),false,408,65⟩,
  ⟨.left,192,0,(-1),false,13,242⟩,
  ⟨.left,193,0,(-1),false,14,248⟩,
  ⟨.left,194,0,(-1),false,15,214⟩,
  ⟨.left,195,0,(-1),false,10,224⟩,
  ⟨.left,196,0,(-1),false,4,230⟩,
  ⟨.left,196,1,(-1),false,2,230⟩,
  ⟨.left,196,2,(-1),false,3,230⟩,
  ⟨.left,196,3,(-1),false,1,230⟩,
  ⟨.left,197,0,(-1),false,6,236⟩,
  ⟨.left,197,1,(-1),false,5,236⟩,
  ⟨.left,198,0,(-1),false,516,289⟩,
  ⟨.left,198,1,(-1),false,515,295⟩,
  ⟨.left,199,0,(-1),false,494,1183⟩,
  ⟨.left,200,0,(-1),false,221,1129⟩,
  ⟨.left,201,0,(-1),false,219,1135⟩,
  ⟨.left,201,1,(-1),false,215,1135⟩,
  ⟨.left,201,2,(-1),false,217,1135⟩,
  ⟨.left,201,3,(-1),false,213,1135⟩,
  ⟨.left,202,0,(-1),false,227,1171⟩,
  ⟨.left,202,1,(-1),false,225,1171⟩,
  ⟨.left,203,0,(-1),false,207,1153⟩,
  ⟨.left,204,0,(-1),false,209,1171⟩,
  ⟨.left,205,0,(-1),false,511,1189⟩,
  ⟨.left,206,0,(-1),false,117,1141⟩,
  ⟨.left,207,0,(-1),false,114,1159⟩,
  ⟨.left,207,1,(-1),false,108,1159⟩,
  ⟨.left,207,2,(-1),false,111,1159⟩,
  ⟨.left,207,3,(-1),false,105,1159⟩,
  ⟨.left,208,0,(-1),false,126,1177⟩,
  ⟨.left,208,1,(-1),false,123,1177⟩,
  ⟨.left,209,0,(-1),false,99,1147⟩,
  ⟨.left,210,0,(-1),false,93,1165⟩,
  ⟨.left,211,0,(-1),false,96,1177⟩,
  ⟨.left,212,0,(-1),false,345,934⟩,
  ⟨.left,213,0,(-1),false,346,970⟩,
  ⟨.left,214,0,(-1),false,339,814⟩,
  ⟨.left,215,0,(-1),false,336,820⟩,
  ⟨.left,215,1,(-1),false,334,820⟩,
  ⟨.left,215,2,(-1),false,335,820⟩,
  ⟨.left,215,3,(-1),false,333,820⟩,
  ⟨.left,216,0,(-1),false,338,856⟩,
  ⟨.left,216,1,(-1),false,337,856⟩,
  ⟨.left,217,0,(-1),false,422,970⟩,
  ⟨.left,217,1,(-1),false,421,970⟩,
  ⟨.left,218,0,(-1),false,222,880⟩,
  ⟨.left,219,0,(-1),false,220,910⟩,
  ⟨.left,219,1,(-1),false,216,910⟩,
  ⟨.left,219,2,(-1),false,218,910⟩,
  ⟨.left,219,3,(-1),false,214,910⟩,
  ⟨.left,220,0,(-1),false,228,970⟩,
  ⟨.left,220,1,(-1),false,226,970⟩,
  ⟨.left,221,0,(-1),false,208,934⟩,
  ⟨.left,222,0,(-1),false,210,970⟩,
  ⟨.left,223,0,(-1),false,512,1021⟩,
  ⟨.left,224,0,(-1),false,296,928⟩,
  ⟨.left,224,1,(-1),false,294,928⟩,
  ⟨.left,224,2,(-1),false,295,928⟩,
  ⟨.left,224,3,(-1),false,293,928⟩,
  ⟨.left,225,0,(-1),false,288,958⟩,
  ⟨.left,225,1,(-1),false,286,958⟩,
  ⟨.left,225,2,(-1),false,287,958⟩,
  ⟨.left,225,3,(-1),false,285,958⟩,
  ⟨.left,226,0,(-1),false,292,988⟩,
  ⟨.left,226,1,(-1),false,290,988⟩,
  ⟨.left,226,2,(-1),false,291,988⟩,
  ⟨.left,226,3,(-1),false,289,988⟩,
  ⟨.left,227,0,(-1),false,264,826⟩,
  ⟨.left,227,1,(-1),false,262,826⟩,
  ⟨.left,227,2,(-1),false,263,826⟩,
  ⟨.left,227,3,(-1),false,261,826⟩,
  ⟨.left,228,0,(-1),false,252,844⟩,
  ⟨.left,228,1,(-1),false,244,844⟩,
  ⟨.left,228,2,(-1),false,248,844⟩,
  ⟨.left,228,3,(-1),false,240,844⟩,
  ⟨.left,228,4,(-1),false,250,844⟩,
  ⟨.left,228,5,(-1),false,242,844⟩,
  ⟨.left,228,6,(-1),false,246,844⟩,
  ⟨.left,228,7,(-1),false,238,844⟩,
  ⟨.left,228,8,(-1),false,251,844⟩,
  ⟨.left,228,9,(-1),false,243,844⟩,
  ⟨.left,228,10,(-1),false,247,844⟩,
  ⟨.left,228,11,(-1),false,239,844⟩,
  ⟨.left,228,12,(-1),false,249,844⟩,
  ⟨.left,228,13,(-1),false,241,844⟩,
  ⟨.left,228,14,(-1),false,245,844⟩,
  ⟨.left,228,15,(-1),false,237,844⟩,
  ⟨.left,229,0,(-1),false,260,886⟩,
  ⟨.left,229,1,(-1),false,256,886⟩,
  ⟨.left,229,2,(-1),false,258,886⟩,
  ⟨.left,229,3,(-1),false,254,886⟩,
  ⟨.left,229,4,(-1),false,259,886⟩,
  ⟨.left,229,5,(-1),false,255,886⟩,
  ⟨.left,229,6,(-1),false,257,886⟩,
  ⟨.left,229,7,(-1),false,253,886⟩,
  ⟨.left,230,0,(-1),false,430,988⟩,
  ⟨.left,230,1,(-1),false,426,988⟩,
  ⟨.left,230,2,(-1),false,428,988⟩,
  ⟨.left,230,3,(-1),false,424,988⟩,
  ⟨.left,230,4,(-1),false,429,988⟩,
  ⟨.left,230,5,(-1),false,425,988⟩,
  ⟨.left,230,6,(-1),false,427,988⟩,
  ⟨.left,230,7,(-1),false,423,988⟩,
  ⟨.left,231,0,(-1),false,118,922⟩,
  ⟨.left,231,1,(-1),false,116,922⟩,
  ⟨.left,232,0,(-1),false,115,952⟩,
  ⟨.left,232,1,(-1),false,109,952⟩,
  ⟨.left,232,2,(-1),false,112,952⟩,
  ⟨.left,232,3,(-1),false,106,952⟩,
  ⟨.left,232,4,(-1),false,113,952⟩,
  ⟨.left,232,5,(-1),false,107,952⟩,
  ⟨.left,232,6,(-1),false,110,952⟩,
  ⟨.left,232,7,(-1),false,104,952⟩,
  ⟨.left,233,0,(-1),false,127,988⟩,
  ⟨.left,233,1,(-1),false,124,988⟩,
  ⟨.left,233,2,(-1),false,125,988⟩,
  ⟨.left,233,3,(-1),false,122,988⟩,
  ⟨.left,234,0,(-1),false,100,928⟩,
  ⟨.left,234,1,(-1),false,98,928⟩,
  ⟨.left,235,0,(-1),false,94,958⟩,
  ⟨.left,235,1,(-1),false,92,958⟩,
  ⟨.left,236,0,(-1),false,97,988⟩,
  ⟨.left,236,1,(-1),false,95,988⟩,
  ⟨.left,237,0,(-1),false,513,11⟩,
  ⟨.left,237,1,0,false,509,8⟩,
  ⟨.left,237,1,1,false,503,47⟩,
  ⟨.left,237,1,2,false,505,577⟩,
  ⟨.left,237,1,3,false,507,277⟩,
  ⟨.left,237,1,4,false,453,1⟩,
  ⟨.left,237,1,5,false,450,33⟩,
  ⟨.left,237,1,6,false,451,563⟩,
  ⟨.left,237,1,7,false,452,263⟩,
  ⟨.left,237,1,8,false,501,303⟩,
  ⟨.left,237,1,9,false,495,37⟩,
  ⟨.left,237,1,10,false,497,567⟩,
  ⟨.left,237,1,11,false,498,267⟩,
  ⟨.left,237,1,12,false,502,4⟩,
  ⟨.left,237,1,13,false,496,41⟩,
  ⟨.left,237,1,14,false,499,571⟩,
  ⟨.left,237,1,15,false,500,271⟩,
  ⟨.left,238,0,(-1),false,202,964⟩,
  ⟨.left,238,1,(-1),false,201,134⟩,
  ⟨.left,239,0,(-1),false,200,982⟩,
  ⟨.left,239,1,(-1),false,199,140⟩,
  ⟨.left,240,0,(-1),false,204,1002⟩,
  ⟨.left,240,1,(-1),false,203,146⟩,
  ⟨.left,241,0,(-1),false,190,868⟩,
  ⟨.left,241,1,(-1),false,189,116⟩,
  ⟨.left,242,0,(-1),false,178,898⟩,
  ⟨.left,242,1,(-1),false,174,898⟩,
  ⟨.left,242,2,(-1),false,176,898⟩,
  ⟨.left,242,3,(-1),false,172,898⟩,
  ⟨.left,242,4,(-1),false,177,122⟩,
  ⟨.left,242,5,(-1),false,173,122⟩,
  ⟨.left,242,6,(-1),false,175,122⟩,
  ⟨.left,242,7,(-1),false,171,122⟩,
  ⟨.left,243,0,(-1),false,182,940⟩,
  ⟨.left,243,1,(-1),false,180,940⟩,
  ⟨.left,243,2,(-1),false,181,128⟩,
  ⟨.left,243,3,(-1),false,179,128⟩,
  ⟨.left,244,0,(-1),false,434,1002⟩,
  ⟨.left,244,1,(-1),false,432,63⟩,
  ⟨.left,244,2,(-1),false,433,146⟩,
  ⟨.left,244,3,(-1),false,431,146⟩,
  ⟨.left,245,0,(-1),false,55,976⟩,
  ⟨.left,246,0,(-1),false,40,994⟩,
  ⟨.left,246,1,(-1),false,38,994⟩,
  ⟨.left,246,2,(-1),false,39,994⟩,
  ⟨.left,246,3,(-1),false,37,994⟩,
  ⟨.left,247,0,(-1),false,42,1002⟩,
  ⟨.left,247,1,(-1),false,41,63⟩,
  ⟨.left,248,0,(-1),false,22,964⟩,
  ⟨.left,249,0,(-1),false,21,982⟩,
  ⟨.left,250,0,(-1),false,23,1002⟩,
  ⟨.left,251,0,(-1),false,514,194⟩,
  ⟨.left,252,0,(-1),false,418,976⟩,
  ⟨.left,252,1,(-1),false,411,976⟩,
  ⟨.left,252,2,(-1),false,419,976⟩,
  ⟨.left,253,0,(-1),false,389,874⟩,
  ⟨.left,253,1,(-1),false,388,874⟩,
  ⟨.left,253,2,(-1),false,390,874⟩,
  ⟨.left,254,0,(-1),false,393,916⟩,
  ⟨.left,254,1,(-1),false,392,916⟩,
  ⟨.left,254,2,(-1),false,394,916⟩,
  ⟨.left,255,0,(-1),false,401,976⟩,
  ⟨.left,255,1,(-1),false,400,976⟩,
  ⟨.left,255,2,(-1),false,402,976⟩,
  ⟨.left,256,0,(-1),false,361,832⟩,
  ⟨.left,256,1,(-1),false,353,832⟩,
  ⟨.left,256,2,(-1),false,357,832⟩,
  ⟨.left,256,3,(-1),false,349,832⟩,
  ⟨.left,256,4,(-1),false,360,832⟩,
  ⟨.left,256,5,(-1),false,352,832⟩,
  ⟨.left,256,6,(-1),false,356,832⟩,
  ⟨.left,256,7,(-1),false,348,832⟩,
  ⟨.left,256,8,(-1),false,362,832⟩,
  ⟨.left,256,9,(-1),false,354,832⟩,
  ⟨.left,256,10,(-1),false,358,832⟩,
  ⟨.left,256,11,(-1),false,350,832⟩,
  ⟨.left,257,0,(-1),false,369,862⟩,
  ⟨.left,257,1,(-1),false,365,862⟩,
  ⟨.left,257,2,(-1),false,368,862⟩,
  ⟨.left,257,3,(-1),false,364,862⟩,
  ⟨.left,257,4,(-1),false,370,862⟩,
  ⟨.left,257,5,(-1),false,366,862⟩,
  ⟨.left,258,0,(-1),false,406,994⟩,
  ⟨.left,258,1,(-1),false,404,994⟩,
  ⟨.left,259,0,(-1),false,325,904⟩,
  ⟨.left,260,0,(-1),false,327,946⟩,
  ⟨.left,261,0,(-1),false,329,994⟩,
  ⟨.left,262,0,(-1),false,323,838⟩,
  ⟨.left,263,0,(-1),false,307,850⟩,
  ⟨.left,263,1,(-1),false,303,850⟩,
  ⟨.left,263,2,(-1),false,305,850⟩,
  ⟨.left,263,3,(-1),false,301,850⟩,
  ⟨.left,264,0,(-1),false,311,892⟩,
  ⟨.left,264,1,(-1),false,309,892⟩,
  ⟨.left,265,0,(-1),false,34,976⟩,
  ⟨.left,266,0,(-1),false,28,994⟩,
  ⟨.left,266,1,(-1),false,26,994⟩,
  ⟨.left,266,2,(-1),false,27,994⟩,
  ⟨.left,266,3,(-1),false,25,994⟩,
  ⟨.left,267,0,(-1),false,30,1002⟩,
  ⟨.left,267,1,(-1),false,29,63⟩,
  ⟨.left,268,0,(-1),false,18,964⟩,
  ⟨.left,269,0,(-1),false,17,982⟩,
  ⟨.left,270,0,(-1),false,19,1002⟩,
  ⟨.left,271,0,(-1),false,391,874⟩,
  ⟨.left,272,0,(-1),false,395,916⟩,
  ⟨.left,273,0,(-1),false,403,976⟩,
  ⟨.left,274,0,(-1),false,363,832⟩,
  ⟨.left,274,1,(-1),false,355,832⟩,
  ⟨.left,274,2,(-1),false,359,832⟩,
  ⟨.left,274,3,(-1),false,351,832⟩,
  ⟨.left,275,0,(-1),false,371,862⟩,
  ⟨.left,275,1,(-1),false,367,862⟩,
  ⟨.left,276,0,(-1),false,420,976⟩,
  ⟨.left,277,0,(-1),false,326,904⟩,
  ⟨.left,278,0,(-1),false,328,946⟩,
  ⟨.left,279,0,(-1),false,330,994⟩,
  ⟨.left,280,0,(-1),false,324,838⟩,
  ⟨.left,281,0,(-1),false,308,850⟩,
  ⟨.left,281,1,(-1),false,304,850⟩,
  ⟨.left,281,2,(-1),false,306,850⟩,
  ⟨.left,281,3,(-1),false,302,850⟩,
  ⟨.left,282,0,(-1),false,312,892⟩,
  ⟨.left,282,1,(-1),false,310,892⟩,
  ⟨.left,283,0,(-1),false,407,994⟩,
  ⟨.left,283,1,(-1),false,405,994⟩,
  ⟨.left,284,0,(-1),false,196,964⟩,
  ⟨.left,285,0,(-1),false,195,982⟩,
  ⟨.left,286,0,(-1),false,197,1002⟩,
  ⟨.left,287,0,(-1),false,168,868⟩,
  ⟨.left,288,0,(-1),false,162,898⟩,
  ⟨.left,288,1,(-1),false,160,898⟩,
  ⟨.left,288,2,(-1),false,161,898⟩,
  ⟨.left,288,3,(-1),false,159,898⟩,
  ⟨.left,289,0,(-1),false,164,940⟩,
  ⟨.left,289,1,(-1),false,163,940⟩,
  ⟨.left,290,0,(-1),false,409,1002⟩,
  ⟨.left,290,1,(-1),false,408,63⟩,
  ⟨.left,291,0,(-1),false,13,240⟩,
  ⟨.left,292,0,(-1),false,14,246⟩,
  ⟨.left,293,0,(-1),false,15,212⟩,
  ⟨.left,294,0,(-1),false,10,222⟩,
  ⟨.left,295,0,(-1),false,4,228⟩,
  ⟨.left,295,1,(-1),false,2,228⟩,
  ⟨.left,295,2,(-1),false,3,228⟩,
  ⟨.left,295,3,(-1),false,1,228⟩,
  ⟨.left,296,0,(-1),false,6,234⟩,
  ⟨.left,296,1,(-1),false,5,234⟩,
  ⟨.left,297,0,(-1),false,516,287⟩,
  ⟨.left,297,1,(-1),false,515,293⟩,
  ⟨.left,298,0,(-1),false,494,1187⟩,
  ⟨.left,299,0,(-1),false,221,1133⟩,
  ⟨.left,300,0,(-1),false,219,1139⟩,
  ⟨.left,300,1,(-1),false,215,1139⟩,
  ⟨.left,300,2,(-1),false,217,1139⟩,
  ⟨.left,300,3,(-1),false,213,1139⟩,
  ⟨.left,301,0,(-1),false,227,1175⟩,
  ⟨.left,301,1,(-1),false,225,1175⟩,
  ⟨.left,302,0,(-1),false,207,1157⟩,
  ⟨.left,303,0,(-1),false,209,1175⟩,
  ⟨.left,304,0,(-1),false,511,1193⟩,
  ⟨.left,305,0,(-1),false,117,1145⟩,
  ⟨.left,306,0,(-1),false,114,1163⟩,
  ⟨.left,306,1,(-1),false,108,1163⟩,
  ⟨.left,306,2,(-1),false,111,1163⟩,
  ⟨.left,306,3,(-1),false,105,1163⟩,
  ⟨.left,307,0,(-1),false,126,1181⟩,
  ⟨.left,307,1,(-1),false,123,1181⟩,
  ⟨.left,308,0,(-1),false,99,1151⟩,
  ⟨.left,309,0,(-1),false,93,1169⟩,
  ⟨.left,310,0,(-1),false,96,1181⟩,
  ⟨.left,311,0,(-1),false,345,938⟩,
  ⟨.left,312,0,(-1),false,346,974⟩,
  ⟨.left,313,0,(-1),false,339,818⟩,
  ⟨.left,314,0,(-1),false,336,824⟩,
  ⟨.left,314,1,(-1),false,334,824⟩,
  ⟨.left,314,2,(-1),false,335,824⟩,
  ⟨.left,314,3,(-1),false,333,824⟩,
  ⟨.left,315,0,(-1),false,338,860⟩,
  ⟨.left,315,1,(-1),false,337,860⟩,
  ⟨.left,316,0,(-1),false,422,974⟩,
  ⟨.left,316,1,(-1),false,421,974⟩,
  ⟨.left,317,0,(-1),false,222,884⟩,
  ⟨.left,318,0,(-1),false,220,914⟩,
  ⟨.left,318,1,(-1),false,216,914⟩,
  ⟨.left,318,2,(-1),false,218,914⟩,
  ⟨.left,318,3,(-1),false,214,914⟩,
  ⟨.left,319,0,(-1),false,228,974⟩,
  ⟨.left,319,1,(-1),false,226,974⟩,
  ⟨.left,320,0,(-1),false,208,938⟩,
  ⟨.left,321,0,(-1),false,210,974⟩,
  ⟨.left,322,0,(-1),false,512,1025⟩,
  ⟨.left,323,0,(-1),false,296,932⟩,
  ⟨.left,323,1,(-1),false,294,932⟩,
  ⟨.left,323,2,(-1),false,295,932⟩,
  ⟨.left,323,3,(-1),false,293,932⟩,
  ⟨.left,324,0,(-1),false,288,962⟩,
  ⟨.left,324,1,(-1),false,286,962⟩,
  ⟨.left,324,2,(-1),false,287,962⟩,
  ⟨.left,324,3,(-1),false,285,962⟩,
  ⟨.left,325,0,(-1),false,292,992⟩,
  ⟨.left,325,1,(-1),false,290,992⟩,
  ⟨.left,325,2,(-1),false,291,992⟩,
  ⟨.left,325,3,(-1),false,289,992⟩,
  ⟨.left,326,0,(-1),false,264,830⟩,
  ⟨.left,326,1,(-1),false,262,830⟩,
  ⟨.left,326,2,(-1),false,263,830⟩,
  ⟨.left,326,3,(-1),false,261,830⟩,
  ⟨.left,327,0,(-1),false,252,848⟩,
  ⟨.left,327,1,(-1),false,244,848⟩,
  ⟨.left,327,2,(-1),false,248,848⟩,
  ⟨.left,327,3,(-1),false,240,848⟩,
  ⟨.left,327,4,(-1),false,250,848⟩,
  ⟨.left,327,5,(-1),false,242,848⟩,
  ⟨.left,327,6,(-1),false,246,848⟩,
  ⟨.left,327,7,(-1),false,238,848⟩,
  ⟨.left,327,8,(-1),false,251,848⟩,
  ⟨.left,327,9,(-1),false,243,848⟩,
  ⟨.left,327,10,(-1),false,247,848⟩,
  ⟨.left,327,11,(-1),false,239,848⟩,
  ⟨.left,327,12,(-1),false,249,848⟩,
  ⟨.left,327,13,(-1),false,241,848⟩,
  ⟨.left,327,14,(-1),false,245,848⟩,
  ⟨.left,327,15,(-1),false,237,848⟩,
  ⟨.left,328,0,(-1),false,260,890⟩,
  ⟨.left,328,1,(-1),false,256,890⟩,
  ⟨.left,328,2,(-1),false,258,890⟩,
  ⟨.left,328,3,(-1),false,254,890⟩,
  ⟨.left,328,4,(-1),false,259,890⟩,
  ⟨.left,328,5,(-1),false,255,890⟩,
  ⟨.left,328,6,(-1),false,257,890⟩,
  ⟨.left,328,7,(-1),false,253,890⟩,
  ⟨.left,329,0,(-1),false,430,992⟩,
  ⟨.left,329,1,(-1),false,426,992⟩,
  ⟨.left,329,2,(-1),false,428,992⟩,
  ⟨.left,329,3,(-1),false,424,992⟩,
  ⟨.left,329,4,(-1),false,429,992⟩,
  ⟨.left,329,5,(-1),false,425,992⟩,
  ⟨.left,329,6,(-1),false,427,992⟩,
  ⟨.left,329,7,(-1),false,423,992⟩,
  ⟨.left,330,0,(-1),false,118,926⟩,
  ⟨.left,330,1,(-1),false,116,926⟩,
  ⟨.left,331,0,(-1),false,115,956⟩,
  ⟨.left,331,1,(-1),false,109,956⟩,
  ⟨.left,331,2,(-1),false,112,956⟩,
  ⟨.left,331,3,(-1),false,106,956⟩,
  ⟨.left,331,4,(-1),false,113,956⟩,
  ⟨.left,331,5,(-1),false,107,956⟩,
  ⟨.left,331,6,(-1),false,110,956⟩,
  ⟨.left,331,7,(-1),false,104,956⟩,
  ⟨.left,332,0,(-1),false,127,992⟩,
  ⟨.left,332,1,(-1),false,124,992⟩,
  ⟨.left,332,2,(-1),false,125,992⟩,
  ⟨.left,332,3,(-1),false,122,992⟩,
  ⟨.left,333,0,(-1),false,100,932⟩,
  ⟨.left,333,1,(-1),false,98,932⟩,
  ⟨.left,334,0,(-1),false,94,962⟩,
  ⟨.left,334,1,(-1),false,92,962⟩,
  ⟨.left,335,0,(-1),false,97,992⟩,
  ⟨.left,335,1,(-1),false,95,992⟩,
  ⟨.left,336,0,(-1),false,513,1049⟩,
  ⟨.left,336,1,0,false,510,1016⟩,
  ⟨.left,336,1,1,false,504,45⟩,
  ⟨.left,336,1,2,false,506,575⟩,
  ⟨.left,336,1,3,false,508,275⟩,
  ⟨.left,337,0,(-1),false,202,968⟩,
  ⟨.left,337,1,(-1),false,201,138⟩,
  ⟨.left,338,0,(-1),false,200,986⟩,
  ⟨.left,338,1,(-1),false,199,144⟩,
  ⟨.left,339,0,(-1),false,204,1006⟩,
  ⟨.left,339,1,(-1),false,203,150⟩,
  ⟨.left,340,0,(-1),false,190,872⟩,
  ⟨.left,340,1,(-1),false,189,120⟩,
  ⟨.left,341,0,(-1),false,178,902⟩,
  ⟨.left,341,1,(-1),false,174,902⟩,
  ⟨.left,341,2,(-1),false,176,902⟩,
  ⟨.left,341,3,(-1),false,172,902⟩,
  ⟨.left,341,4,(-1),false,177,126⟩,
  ⟨.left,341,5,(-1),false,173,126⟩,
  ⟨.left,341,6,(-1),false,175,126⟩,
  ⟨.left,341,7,(-1),false,171,126⟩,
  ⟨.left,342,0,(-1),false,182,944⟩,
  ⟨.left,342,1,(-1),false,180,944⟩,
  ⟨.left,342,2,(-1),false,181,132⟩,
  ⟨.left,342,3,(-1),false,179,132⟩,
  ⟨.left,343,0,(-1),false,434,1006⟩,
  ⟨.left,343,1,(-1),false,432,67⟩,
  ⟨.left,343,2,(-1),false,433,150⟩,
  ⟨.left,343,3,(-1),false,431,150⟩,
  ⟨.left,344,0,(-1),false,55,980⟩,
  ⟨.left,345,0,(-1),false,40,998⟩,
  ⟨.left,345,1,(-1),false,38,998⟩,
  ⟨.left,345,2,(-1),false,39,998⟩,
  ⟨.left,345,3,(-1),false,37,998⟩,
  ⟨.left,346,0,(-1),false,42,1006⟩,
  ⟨.left,346,1,(-1),false,41,67⟩,
  ⟨.left,347,0,(-1),false,22,968⟩,
  ⟨.left,348,0,(-1),false,21,986⟩,
  ⟨.left,349,0,(-1),false,23,1006⟩,
  ⟨.left,350,0,(-1),false,514,198⟩,
  ⟨.left,351,0,(-1),false,418,980⟩,
  ⟨.left,351,1,(-1),false,411,980⟩,
  ⟨.left,351,2,(-1),false,419,980⟩,
  ⟨.left,352,0,(-1),false,389,878⟩,
  ⟨.left,352,1,(-1),false,388,878⟩,
  ⟨.left,352,2,(-1),false,390,878⟩,
  ⟨.left,353,0,(-1),false,393,920⟩,
  ⟨.left,353,1,(-1),false,392,920⟩,
  ⟨.left,353,2,(-1),false,394,920⟩,
  ⟨.left,354,0,(-1),false,401,980⟩,
  ⟨.left,354,1,(-1),false,400,980⟩,
  ⟨.left,354,2,(-1),false,402,980⟩,
  ⟨.left,355,0,(-1),false,361,836⟩,
  ⟨.left,355,1,(-1),false,353,836⟩,
  ⟨.left,355,2,(-1),false,357,836⟩,
  ⟨.left,355,3,(-1),false,349,836⟩,
  ⟨.left,355,4,(-1),false,360,836⟩,
  ⟨.left,355,5,(-1),false,352,836⟩,
  ⟨.left,355,6,(-1),false,356,836⟩,
  ⟨.left,355,7,(-1),false,348,836⟩,
  ⟨.left,355,8,(-1),false,362,836⟩,
  ⟨.left,355,9,(-1),false,354,836⟩,
  ⟨.left,355,10,(-1),false,358,836⟩,
  ⟨.left,355,11,(-1),false,350,836⟩,
  ⟨.left,356,0,(-1),false,369,866⟩,
  ⟨.left,356,1,(-1),false,365,866⟩,
  ⟨.left,356,2,(-1),false,368,866⟩,
  ⟨.left,356,3,(-1),false,364,866⟩,
  ⟨.left,356,4,(-1),false,370,866⟩,
  ⟨.left,356,5,(-1),false,366,866⟩,
  ⟨.left,357,0,(-1),false,406,998⟩,
  ⟨.left,357,1,(-1),false,404,998⟩,
  ⟨.left,358,0,(-1),false,325,908⟩,
  ⟨.left,359,0,(-1),false,327,950⟩,
  ⟨.left,360,0,(-1),false,329,998⟩,
  ⟨.left,361,0,(-1),false,323,842⟩,
  ⟨.left,362,0,(-1),false,307,854⟩,
  ⟨.left,362,1,(-1),false,303,854⟩,
  ⟨.left,362,2,(-1),false,305,854⟩,
  ⟨.left,362,3,(-1),false,301,854⟩,
  ⟨.left,363,0,(-1),false,311,896⟩,
  ⟨.left,363,1,(-1),false,309,896⟩,
  ⟨.left,364,0,(-1),false,34,980⟩,
  ⟨.left,365,0,(-1),false,28,998⟩,
  ⟨.left,365,1,(-1),false,26,998⟩,
  ⟨.left,365,2,(-1),false,27,998⟩,
  ⟨.left,365,3,(-1),false,25,998⟩,
  ⟨.left,366,0,(-1),false,30,1006⟩,
  ⟨.left,366,1,(-1),false,29,67⟩,
  ⟨.left,367,0,(-1),false,18,968⟩,
  ⟨.left,368,0,(-1),false,17,986⟩,
  ⟨.left,369,0,(-1),false,19,1006⟩,
  ⟨.left,370,0,(-1),false,391,878⟩,
  ⟨.left,371,0,(-1),false,395,920⟩,
  ⟨.left,372,0,(-1),false,403,980⟩,
  ⟨.left,373,0,(-1),false,363,836⟩,
  ⟨.left,373,1,(-1),false,355,836⟩,
  ⟨.left,373,2,(-1),false,359,836⟩,
  ⟨.left,373,3,(-1),false,351,836⟩,
  ⟨.left,374,0,(-1),false,371,866⟩,
  ⟨.left,374,1,(-1),false,367,866⟩,
  ⟨.left,375,0,(-1),false,420,980⟩,
  ⟨.left,376,0,(-1),false,326,908⟩,
  ⟨.left,377,0,(-1),false,328,950⟩,
  ⟨.left,378,0,(-1),false,330,998⟩,
  ⟨.left,379,0,(-1),false,324,842⟩,
  ⟨.left,380,0,(-1),false,308,854⟩,
  ⟨.left,380,1,(-1),false,304,854⟩,
  ⟨.left,380,2,(-1),false,306,854⟩,
  ⟨.left,380,3,(-1),false,302,854⟩,
  ⟨.left,381,0,(-1),false,312,896⟩,
  ⟨.left,381,1,(-1),false,310,896⟩,
  ⟨.left,382,0,(-1),false,407,998⟩,
  ⟨.left,382,1,(-1),false,405,998⟩,
  ⟨.left,383,0,(-1),false,196,968⟩,
  ⟨.left,384,0,(-1),false,195,986⟩,
  ⟨.left,385,0,(-1),false,197,1006⟩,
  ⟨.left,386,0,(-1),false,168,872⟩,
  ⟨.left,387,0,(-1),false,162,902⟩,
  ⟨.left,387,1,(-1),false,160,902⟩,
  ⟨.left,387,2,(-1),false,161,902⟩,
  ⟨.left,387,3,(-1),false,159,902⟩,
  ⟨.left,388,0,(-1),false,164,944⟩,
  ⟨.left,388,1,(-1),false,163,944⟩,
  ⟨.left,389,0,(-1),false,409,1006⟩,
  ⟨.left,389,1,(-1),false,408,67⟩,
  ⟨.left,390,0,(-1),false,13,244⟩,
  ⟨.left,391,0,(-1),false,14,216⟩,
  ⟨.left,392,0,(-1),false,15,216⟩,
  ⟨.left,393,0,(-1),false,10,226⟩,
  ⟨.left,394,0,(-1),false,4,232⟩,
  ⟨.left,394,1,(-1),false,2,232⟩,
  ⟨.left,394,2,(-1),false,3,232⟩,
  ⟨.left,394,3,(-1),false,1,232⟩,
  ⟨.left,395,0,(-1),false,6,238⟩,
  ⟨.left,395,1,(-1),false,5,238⟩,
  ⟨.left,396,0,(-1),false,516,291⟩,
  ⟨.left,396,1,(-1),false,515,297⟩,
  ⟨.left,397,0,(-1),false,494,1184⟩,
  ⟨.left,398,0,(-1),false,221,1130⟩,
  ⟨.left,399,0,(-1),false,219,1136⟩,
  ⟨.left,399,1,(-1),false,215,1136⟩,
  ⟨.left,399,2,(-1),false,217,1136⟩,
  ⟨.left,399,3,(-1),false,213,1136⟩,
  ⟨.left,400,0,(-1),false,227,1172⟩,
  ⟨.left,400,1,(-1),false,225,1172⟩,
  ⟨.left,401,0,(-1),false,207,1154⟩,
  ⟨.left,402,0,(-1),false,209,1172⟩,
  ⟨.left,403,0,(-1),false,511,1190⟩,
  ⟨.left,404,0,(-1),false,117,1142⟩,
  ⟨.left,405,0,(-1),false,114,1160⟩,
  ⟨.left,405,1,(-1),false,108,1160⟩,
  ⟨.left,405,2,(-1),false,111,1160⟩,
  ⟨.left,405,3,(-1),false,105,1160⟩,
  ⟨.left,406,0,(-1),false,126,1178⟩,
  ⟨.left,406,1,(-1),false,123,1178⟩,
  ⟨.left,407,0,(-1),false,99,1148⟩,
  ⟨.left,408,0,(-1),false,93,1166⟩,
  ⟨.left,409,0,(-1),false,96,1178⟩,
  ⟨.left,410,0,(-1),false,345,935⟩,
  ⟨.left,411,0,(-1),false,346,971⟩,
  ⟨.left,412,0,(-1),false,339,815⟩,
  ⟨.left,413,0,(-1),false,336,821⟩,
  ⟨.left,413,1,(-1),false,334,821⟩,
  ⟨.left,413,2,(-1),false,335,821⟩,
  ⟨.left,413,3,(-1),false,333,821⟩,
  ⟨.left,414,0,(-1),false,338,857⟩,
  ⟨.left,414,1,(-1),false,337,857⟩,
  ⟨.left,415,0,(-1),false,422,971⟩,
  ⟨.left,415,1,(-1),false,421,971⟩,
  ⟨.left,416,0,(-1),false,222,881⟩,
  ⟨.left,417,0,(-1),false,220,911⟩,
  ⟨.left,417,1,(-1),false,216,911⟩,
  ⟨.left,417,2,(-1),false,218,911⟩,
  ⟨.left,417,3,(-1),false,214,911⟩,
  ⟨.left,418,0,(-1),false,228,971⟩,
  ⟨.left,418,1,(-1),false,226,971⟩,
  ⟨.left,419,0,(-1),false,208,935⟩,
  ⟨.left,420,0,(-1),false,210,971⟩,
  ⟨.left,421,0,(-1),false,512,1022⟩,
  ⟨.left,422,0,(-1),false,296,929⟩,
  ⟨.left,422,1,(-1),false,294,929⟩,
  ⟨.left,422,2,(-1),false,295,929⟩,
  ⟨.left,422,3,(-1),false,293,929⟩,
  ⟨.left,423,0,(-1),false,288,959⟩,
  ⟨.left,423,1,(-1),false,286,959⟩,
  ⟨.left,423,2,(-1),false,287,959⟩,
  ⟨.left,423,3,(-1),false,285,959⟩,
  ⟨.left,424,0,(-1),false,292,989⟩,
  ⟨.left,424,1,(-1),false,290,989⟩,
  ⟨.left,424,2,(-1),false,291,989⟩,
  ⟨.left,424,3,(-1),false,289,989⟩,
  ⟨.left,425,0,(-1),false,264,827⟩,
  ⟨.left,425,1,(-1),false,262,827⟩,
  ⟨.left,425,2,(-1),false,263,827⟩,
  ⟨.left,425,3,(-1),false,261,827⟩,
  ⟨.left,426,0,(-1),false,252,845⟩,
  ⟨.left,426,1,(-1),false,244,845⟩,
  ⟨.left,426,2,(-1),false,248,845⟩,
  ⟨.left,426,3,(-1),false,240,845⟩,
  ⟨.left,426,4,(-1),false,250,845⟩,
  ⟨.left,426,5,(-1),false,242,845⟩,
  ⟨.left,426,6,(-1),false,246,845⟩,
  ⟨.left,426,7,(-1),false,238,845⟩,
  ⟨.left,426,8,(-1),false,251,845⟩,
  ⟨.left,426,9,(-1),false,243,845⟩,
  ⟨.left,426,10,(-1),false,247,845⟩,
  ⟨.left,426,11,(-1),false,239,845⟩,
  ⟨.left,426,12,(-1),false,249,845⟩,
  ⟨.left,426,13,(-1),false,241,845⟩,
  ⟨.left,426,14,(-1),false,245,845⟩,
  ⟨.left,426,15,(-1),false,237,845⟩,
  ⟨.left,427,0,(-1),false,260,887⟩,
  ⟨.left,427,1,(-1),false,256,887⟩,
  ⟨.left,427,2,(-1),false,258,887⟩,
  ⟨.left,427,3,(-1),false,254,887⟩,
  ⟨.left,427,4,(-1),false,259,887⟩,
  ⟨.left,427,5,(-1),false,255,887⟩,
  ⟨.left,427,6,(-1),false,257,887⟩,
  ⟨.left,427,7,(-1),false,253,887⟩,
  ⟨.left,428,0,(-1),false,430,989⟩,
  ⟨.left,428,1,(-1),false,426,989⟩,
  ⟨.left,428,2,(-1),false,428,989⟩,
  ⟨.left,428,3,(-1),false,424,989⟩,
  ⟨.left,428,4,(-1),false,429,989⟩,
  ⟨.left,428,5,(-1),false,425,989⟩,
  ⟨.left,428,6,(-1),false,427,989⟩,
  ⟨.left,428,7,(-1),false,423,989⟩,
  ⟨.left,429,0,(-1),false,118,923⟩,
  ⟨.left,429,1,(-1),false,116,923⟩,
  ⟨.left,430,0,(-1),false,115,953⟩,
  ⟨.left,430,1,(-1),false,109,953⟩,
  ⟨.left,430,2,(-1),false,112,953⟩,
  ⟨.left,430,3,(-1),false,106,953⟩,
  ⟨.left,430,4,(-1),false,113,953⟩,
  ⟨.left,430,5,(-1),false,107,953⟩,
  ⟨.left,430,6,(-1),false,110,953⟩,
  ⟨.left,430,7,(-1),false,104,953⟩,
  ⟨.left,431,0,(-1),false,127,989⟩,
  ⟨.left,431,1,(-1),false,124,989⟩,
  ⟨.left,431,2,(-1),false,125,989⟩,
  ⟨.left,431,3,(-1),false,122,989⟩,
  ⟨.left,432,0,(-1),false,100,929⟩,
  ⟨.left,432,1,(-1),false,98,929⟩,
  ⟨.left,433,0,(-1),false,94,959⟩,
  ⟨.left,433,1,(-1),false,92,959⟩,
  ⟨.left,434,0,(-1),false,97,989⟩,
  ⟨.left,434,1,(-1),false,95,989⟩,
  ⟨.left,435,0,(-1),false,513,12⟩,
  ⟨.left,435,1,0,false,509,9⟩,
  ⟨.left,435,1,1,false,503,48⟩,
  ⟨.left,435,1,2,false,505,578⟩,
  ⟨.left,435,1,3,false,507,278⟩,
  ⟨.left,435,1,4,false,453,2⟩,
  ⟨.left,435,1,5,false,450,34⟩,
  ⟨.left,435,1,6,false,451,564⟩,
  ⟨.left,435,1,7,false,452,264⟩,
  ⟨.left,435,1,8,false,501,304⟩,
  ⟨.left,435,1,9,false,495,38⟩,
  ⟨.left,435,1,10,false,497,568⟩,
  ⟨.left,435,1,11,false,498,268⟩,
  ⟨.left,435,1,12,false,502,5⟩,
  ⟨.left,435,1,13,false,496,42⟩,
  ⟨.left,435,1,14,false,499,572⟩,
  ⟨.left,435,1,15,false,500,272⟩,
  ⟨.left,436,0,(-1),false,202,965⟩,
  ⟨.left,436,1,(-1),false,201,135⟩,
  ⟨.left,437,0,(-1),false,200,983⟩,
  ⟨.left,437,1,(-1),false,199,141⟩,
  ⟨.left,438,0,(-1),false,204,1003⟩,
  ⟨.left,438,1,(-1),false,203,147⟩,
  ⟨.left,439,0,(-1),false,190,869⟩,
  ⟨.left,439,1,(-1),false,189,117⟩,
  ⟨.left,440,0,(-1),false,178,899⟩,
  ⟨.left,440,1,(-1),false,174,899⟩,
  ⟨.left,440,2,(-1),false,176,899⟩,
  ⟨.left,440,3,(-1),false,172,899⟩,
  ⟨.left,440,4,(-1),false,177,123⟩,
  ⟨.left,440,5,(-1),false,173,123⟩,
  ⟨.left,440,6,(-1),false,175,123⟩,
  ⟨.left,440,7,(-1),false,171,123⟩,
  ⟨.left,441,0,(-1),false,182,941⟩,
  ⟨.left,441,1,(-1),false,180,941⟩,
  ⟨.left,441,2,(-1),false,181,129⟩,
  ⟨.left,441,3,(-1),false,179,129⟩,
  ⟨.left,442,0,(-1),false,434,1003⟩,
  ⟨.left,442,1,(-1),false,432,64⟩,
  ⟨.left,442,2,(-1),false,433,147⟩,
  ⟨.left,442,3,(-1),false,431,147⟩,
  ⟨.left,443,0,(-1),false,55,977⟩,
  ⟨.left,444,0,(-1),false,40,995⟩,
  ⟨.left,444,1,(-1),false,38,995⟩,
  ⟨.left,444,2,(-1),false,39,995⟩,
  ⟨.left,444,3,(-1),false,37,995⟩,
  ⟨.left,445,0,(-1),false,42,1003⟩,
  ⟨.left,445,1,(-1),false,41,64⟩,
  ⟨.left,446,0,(-1),false,22,965⟩,
  ⟨.left,447,0,(-1),false,21,983⟩,
  ⟨.left,448,0,(-1),false,23,1003⟩,
  ⟨.left,449,0,(-1),false,514,195⟩,
  ⟨.left,450,0,(-1),false,418,977⟩,
  ⟨.left,450,1,(-1),false,411,977⟩,
  ⟨.left,450,2,(-1),false,419,977⟩,
  ⟨.left,451,0,(-1),false,389,875⟩,
  ⟨.left,451,1,(-1),false,388,875⟩,
  ⟨.left,451,2,(-1),false,390,875⟩,
  ⟨.left,452,0,(-1),false,393,917⟩,
  ⟨.left,452,1,(-1),false,392,917⟩,
  ⟨.left,452,2,(-1),false,394,917⟩,
  ⟨.left,453,0,(-1),false,401,977⟩,
  ⟨.left,453,1,(-1),false,400,977⟩,
  ⟨.left,453,2,(-1),false,402,977⟩,
  ⟨.left,454,0,(-1),false,361,833⟩,
  ⟨.left,454,1,(-1),false,353,833⟩,
  ⟨.left,454,2,(-1),false,357,833⟩,
  ⟨.left,454,3,(-1),false,349,833⟩,
  ⟨.left,454,4,(-1),false,360,833⟩,
  ⟨.left,454,5,(-1),false,352,833⟩,
  ⟨.left,454,6,(-1),false,356,833⟩,
  ⟨.left,454,7,(-1),false,348,833⟩,
  ⟨.left,454,8,(-1),false,362,833⟩,
  ⟨.left,454,9,(-1),false,354,833⟩,
  ⟨.left,454,10,(-1),false,358,833⟩,
  ⟨.left,454,11,(-1),false,350,833⟩,
  ⟨.left,455,0,(-1),false,369,863⟩,
  ⟨.left,455,1,(-1),false,365,863⟩,
  ⟨.left,455,2,(-1),false,368,863⟩,
  ⟨.left,455,3,(-1),false,364,863⟩,
  ⟨.left,455,4,(-1),false,370,863⟩,
  ⟨.left,455,5,(-1),false,366,863⟩,
  ⟨.left,456,0,(-1),false,406,995⟩,
  ⟨.left,456,1,(-1),false,404,995⟩,
  ⟨.left,457,0,(-1),false,325,905⟩,
  ⟨.left,458,0,(-1),false,327,947⟩,
  ⟨.left,459,0,(-1),false,329,995⟩,
  ⟨.left,460,0,(-1),false,323,839⟩,
  ⟨.left,461,0,(-1),false,307,851⟩,
  ⟨.left,461,1,(-1),false,303,851⟩,
  ⟨.left,461,2,(-1),false,305,851⟩,
  ⟨.left,461,3,(-1),false,301,851⟩,
  ⟨.left,462,0,(-1),false,311,893⟩,
  ⟨.left,462,1,(-1),false,309,893⟩,
  ⟨.left,463,0,(-1),false,34,977⟩,
  ⟨.left,464,0,(-1),false,28,995⟩,
  ⟨.left,464,1,(-1),false,26,995⟩,
  ⟨.left,464,2,(-1),false,27,995⟩,
  ⟨.left,464,3,(-1),false,25,995⟩,
  ⟨.left,465,0,(-1),false,30,1003⟩,
  ⟨.left,465,1,(-1),false,29,64⟩,
  ⟨.left,466,0,(-1),false,18,965⟩,
  ⟨.left,467,0,(-1),false,17,983⟩,
  ⟨.left,468,0,(-1),false,19,1003⟩,
  ⟨.left,469,0,(-1),false,391,875⟩,
  ⟨.left,470,0,(-1),false,395,917⟩,
  ⟨.left,471,0,(-1),false,403,977⟩,
  ⟨.left,472,0,(-1),false,363,833⟩,
  ⟨.left,472,1,(-1),false,355,833⟩,
  ⟨.left,472,2,(-1),false,359,833⟩,
  ⟨.left,472,3,(-1),false,351,833⟩,
  ⟨.left,473,0,(-1),false,371,863⟩,
  ⟨.left,473,1,(-1),false,367,863⟩,
  ⟨.left,474,0,(-1),false,420,977⟩,
  ⟨.left,475,0,(-1),false,326,905⟩,
  ⟨.left,476,0,(-1),false,328,947⟩,
  ⟨.left,477,0,(-1),false,330,995⟩,
  ⟨.left,478,0,(-1),false,324,839⟩,
  ⟨.left,479,0,(-1),false,308,851⟩,
  ⟨.left,479,1,(-1),false,304,851⟩,
  ⟨.left,479,2,(-1),false,306,851⟩,
  ⟨.left,479,3,(-1),false,302,851⟩,
  ⟨.left,480,0,(-1),false,312,893⟩,
  ⟨.left,480,1,(-1),false,310,893⟩,
  ⟨.left,481,0,(-1),false,407,995⟩,
  ⟨.left,481,1,(-1),false,405,995⟩,
  ⟨.left,482,0,(-1),false,196,965⟩,
  ⟨.left,483,0,(-1),false,195,983⟩,
  ⟨.left,484,0,(-1),false,197,1003⟩,
  ⟨.left,485,0,(-1),false,168,869⟩,
  ⟨.left,486,0,(-1),false,162,899⟩,
  ⟨.left,486,1,(-1),false,160,899⟩,
  ⟨.left,486,2,(-1),false,161,899⟩,
  ⟨.left,486,3,(-1),false,159,899⟩,
  ⟨.left,487,0,(-1),false,164,941⟩,
  ⟨.left,487,1,(-1),false,163,941⟩,
  ⟨.left,488,0,(-1),false,409,1003⟩,
  ⟨.left,488,1,(-1),false,408,64⟩,
  ⟨.left,489,0,(-1),false,13,241⟩,
  ⟨.left,490,0,(-1),false,14,247⟩,
  ⟨.left,491,0,(-1),false,15,213⟩,
  ⟨.left,492,0,(-1),false,10,223⟩,
  ⟨.left,493,0,(-1),false,4,229⟩,
  ⟨.left,493,1,(-1),false,2,229⟩,
  ⟨.left,493,2,(-1),false,3,229⟩,
  ⟨.left,493,3,(-1),false,1,229⟩,
  ⟨.left,494,0,(-1),false,6,235⟩,
  ⟨.left,494,1,(-1),false,5,235⟩,
  ⟨.left,495,0,(-1),false,516,288⟩,
  ⟨.left,495,1,(-1),false,515,294⟩,
  ⟨.left,496,0,(-1),false,494,1188⟩,
  ⟨.left,497,0,(-1),false,221,1134⟩,
  ⟨.left,498,0,(-1),false,219,1140⟩,
  ⟨.left,498,1,(-1),false,215,1140⟩,
  ⟨.left,498,2,(-1),false,217,1140⟩,
  ⟨.left,498,3,(-1),false,213,1140⟩,
  ⟨.left,499,0,(-1),false,227,1176⟩,
  ⟨.left,499,1,(-1),false,225,1176⟩,
  ⟨.left,500,0,(-1),false,207,1158⟩,
  ⟨.left,501,0,(-1),false,209,1176⟩,
  ⟨.left,502,0,(-1),false,511,1194⟩,
  ⟨.left,503,0,(-1),false,117,1146⟩,
  ⟨.left,504,0,(-1),false,114,1164⟩,
  ⟨.left,504,1,(-1),false,108,1164⟩,
  ⟨.left,504,2,(-1),false,111,1164⟩,
  ⟨.left,504,3,(-1),false,105,1164⟩,
  ⟨.left,505,0,(-1),false,126,1182⟩,
  ⟨.left,505,1,(-1),false,123,1182⟩,
  ⟨.left,506,0,(-1),false,99,1152⟩,
  ⟨.left,507,0,(-1),false,93,1170⟩,
  ⟨.left,508,0,(-1),false,96,1182⟩,
  ⟨.left,509,0,(-1),false,345,939⟩,
  ⟨.left,510,0,(-1),false,346,975⟩,
  ⟨.left,511,0,(-1),false,339,819⟩,
  ⟨.left,512,0,(-1),false,336,825⟩,
  ⟨.left,512,1,(-1),false,334,825⟩,
  ⟨.left,512,2,(-1),false,335,825⟩,
  ⟨.left,512,3,(-1),false,333,825⟩,
  ⟨.left,513,0,(-1),false,338,861⟩,
  ⟨.left,513,1,(-1),false,337,861⟩,
  ⟨.left,514,0,(-1),false,422,975⟩,
  ⟨.left,514,1,(-1),false,421,975⟩,
  ⟨.left,515,0,(-1),false,222,885⟩,
  ⟨.left,516,0,(-1),false,220,915⟩,
  ⟨.left,516,1,(-1),false,216,915⟩,
  ⟨.left,516,2,(-1),false,218,915⟩,
  ⟨.left,516,3,(-1),false,214,915⟩,
  ⟨.left,517,0,(-1),false,228,975⟩,
  ⟨.left,517,1,(-1),false,226,975⟩,
  ⟨.left,518,0,(-1),false,208,939⟩,
  ⟨.left,519,0,(-1),false,210,975⟩,
  ⟨.left,520,0,(-1),false,512,1026⟩,
  ⟨.left,521,0,(-1),false,296,933⟩,
  ⟨.left,521,1,(-1),false,294,933⟩,
  ⟨.left,521,2,(-1),false,295,933⟩,
  ⟨.left,521,3,(-1),false,293,933⟩,
  ⟨.left,522,0,(-1),false,288,963⟩,
  ⟨.left,522,1,(-1),false,286,963⟩,
  ⟨.left,522,2,(-1),false,287,963⟩,
  ⟨.left,522,3,(-1),false,285,963⟩,
  ⟨.left,523,0,(-1),false,292,993⟩,
  ⟨.left,523,1,(-1),false,290,993⟩,
  ⟨.left,523,2,(-1),false,291,993⟩,
  ⟨.left,523,3,(-1),false,289,993⟩,
  ⟨.left,524,0,(-1),false,264,831⟩,
  ⟨.left,524,1,(-1),false,262,831⟩,
  ⟨.left,524,2,(-1),false,263,831⟩,
  ⟨.left,524,3,(-1),false,261,831⟩,
  ⟨.left,525,0,(-1),false,252,849⟩,
  ⟨.left,525,1,(-1),false,244,849⟩,
  ⟨.left,525,2,(-1),false,248,849⟩,
  ⟨.left,525,3,(-1),false,240,849⟩,
  ⟨.left,525,4,(-1),false,250,849⟩,
  ⟨.left,525,5,(-1),false,242,849⟩,
  ⟨.left,525,6,(-1),false,246,849⟩,
  ⟨.left,525,7,(-1),false,238,849⟩,
  ⟨.left,525,8,(-1),false,251,849⟩,
  ⟨.left,525,9,(-1),false,243,849⟩,
  ⟨.left,525,10,(-1),false,247,849⟩,
  ⟨.left,525,11,(-1),false,239,849⟩,
  ⟨.left,525,12,(-1),false,249,849⟩,
  ⟨.left,525,13,(-1),false,241,849⟩,
  ⟨.left,525,14,(-1),false,245,849⟩,
  ⟨.left,525,15,(-1),false,237,849⟩,
  ⟨.left,526,0,(-1),false,260,891⟩,
  ⟨.left,526,1,(-1),false,256,891⟩,
  ⟨.left,526,2,(-1),false,258,891⟩,
  ⟨.left,526,3,(-1),false,254,891⟩,
  ⟨.left,526,4,(-1),false,259,891⟩,
  ⟨.left,526,5,(-1),false,255,891⟩,
  ⟨.left,526,6,(-1),false,257,891⟩,
  ⟨.left,526,7,(-1),false,253,891⟩,
  ⟨.left,527,0,(-1),false,430,993⟩,
  ⟨.left,527,1,(-1),false,426,993⟩,
  ⟨.left,527,2,(-1),false,428,993⟩,
  ⟨.left,527,3,(-1),false,424,993⟩,
  ⟨.left,527,4,(-1),false,429,993⟩,
  ⟨.left,527,5,(-1),false,425,993⟩,
  ⟨.left,527,6,(-1),false,427,993⟩,
  ⟨.left,527,7,(-1),false,423,993⟩,
  ⟨.left,528,0,(-1),false,118,927⟩,
  ⟨.left,528,1,(-1),false,116,927⟩,
  ⟨.left,529,0,(-1),false,115,957⟩,
  ⟨.left,529,1,(-1),false,109,957⟩,
  ⟨.left,529,2,(-1),false,112,957⟩,
  ⟨.left,529,3,(-1),false,106,957⟩,
  ⟨.left,529,4,(-1),false,113,957⟩,
  ⟨.left,529,5,(-1),false,107,957⟩,
  ⟨.left,529,6,(-1),false,110,957⟩,
  ⟨.left,529,7,(-1),false,104,957⟩,
  ⟨.left,530,0,(-1),false,127,993⟩,
  ⟨.left,530,1,(-1),false,124,993⟩,
  ⟨.left,530,2,(-1),false,125,993⟩,
  ⟨.left,530,3,(-1),false,122,993⟩,
  ⟨.left,531,0,(-1),false,100,933⟩,
  ⟨.left,531,1,(-1),false,98,933⟩,
  ⟨.left,532,0,(-1),false,94,963⟩,
  ⟨.left,532,1,(-1),false,92,963⟩,
  ⟨.left,533,0,(-1),false,97,993⟩,
  ⟨.left,533,1,(-1),false,95,993⟩,
  ⟨.left,534,0,(-1),false,513,14⟩,
  ⟨.left,534,1,0,false,510,7⟩,
  ⟨.left,534,1,1,false,504,46⟩,
  ⟨.left,534,1,2,false,506,576⟩,
  ⟨.left,534,1,3,false,508,276⟩,
  ⟨.left,535,0,(-1),false,202,969⟩,
  ⟨.left,535,1,(-1),false,201,139⟩,
  ⟨.left,536,0,(-1),false,200,987⟩,
  ⟨.left,536,1,(-1),false,199,145⟩,
  ⟨.left,537,0,(-1),false,204,1007⟩,
  ⟨.left,537,1,(-1),false,203,151⟩,
  ⟨.left,538,0,(-1),false,190,873⟩,
  ⟨.left,538,1,(-1),false,189,121⟩,
  ⟨.left,539,0,(-1),false,178,903⟩,
  ⟨.left,539,1,(-1),false,174,903⟩,
  ⟨.left,539,2,(-1),false,176,903⟩,
  ⟨.left,539,3,(-1),false,172,903⟩,
  ⟨.left,539,4,(-1),false,177,127⟩,
  ⟨.left,539,5,(-1),false,173,127⟩,
  ⟨.left,539,6,(-1),false,175,127⟩,
  ⟨.left,539,7,(-1),false,171,127⟩,
  ⟨.left,540,0,(-1),false,182,945⟩,
  ⟨.left,540,1,(-1),false,180,945⟩,
  ⟨.left,540,2,(-1),false,181,133⟩,
  ⟨.left,540,3,(-1),false,179,133⟩,
  ⟨.left,541,0,(-1),false,434,1007⟩,
  ⟨.left,541,1,(-1),false,432,68⟩,
  ⟨.left,541,2,(-1),false,433,151⟩,
  ⟨.left,541,3,(-1),false,431,151⟩,
  ⟨.left,542,0,(-1),false,55,981⟩,
  ⟨.left,543,0,(-1),false,40,999⟩,
  ⟨.left,543,1,(-1),false,38,999⟩,
  ⟨.left,543,2,(-1),false,39,999⟩,
  ⟨.left,543,3,(-1),false,37,999⟩,
  ⟨.left,544,0,(-1),false,42,1007⟩,
  ⟨.left,544,1,(-1),false,41,68⟩,
  ⟨.left,545,0,(-1),false,22,969⟩,
  ⟨.left,546,0,(-1),false,21,987⟩,
  ⟨.left,547,0,(-1),false,23,1007⟩,
  ⟨.left,548,0,(-1),false,514,199⟩,
  ⟨.left,549,0,(-1),false,418,981⟩,
  ⟨.left,549,1,(-1),false,411,981⟩,
  ⟨.left,549,2,(-1),false,419,981⟩,
  ⟨.left,550,0,(-1),false,389,879⟩,
  ⟨.left,550,1,(-1),false,388,879⟩,
  ⟨.left,550,2,(-1),false,390,879⟩,
  ⟨.left,551,0,(-1),false,393,921⟩,
  ⟨.left,551,1,(-1),false,392,921⟩,
  ⟨.left,551,2,(-1),false,394,921⟩,
  ⟨.left,552,0,(-1),false,401,981⟩,
  ⟨.left,552,1,(-1),false,400,981⟩,
  ⟨.left,552,2,(-1),false,402,981⟩,
  ⟨.left,553,0,(-1),false,361,837⟩,
  ⟨.left,553,1,(-1),false,353,837⟩,
  ⟨.left,553,2,(-1),false,357,837⟩,
  ⟨.left,553,3,(-1),false,349,837⟩,
  ⟨.left,553,4,(-1),false,360,837⟩,
  ⟨.left,553,5,(-1),false,352,837⟩,
  ⟨.left,553,6,(-1),false,356,837⟩,
  ⟨.left,553,7,(-1),false,348,837⟩,
  ⟨.left,553,8,(-1),false,362,837⟩,
  ⟨.left,553,9,(-1),false,354,837⟩,
  ⟨.left,553,10,(-1),false,358,837⟩,
  ⟨.left,553,11,(-1),false,350,837⟩,
  ⟨.left,554,0,(-1),false,369,867⟩,
  ⟨.left,554,1,(-1),false,365,867⟩,
  ⟨.left,554,2,(-1),false,368,867⟩,
  ⟨.left,554,3,(-1),false,364,867⟩,
  ⟨.left,554,4,(-1),false,370,867⟩,
  ⟨.left,554,5,(-1),false,366,867⟩,
  ⟨.left,555,0,(-1),false,406,999⟩,
  ⟨.left,555,1,(-1),false,404,999⟩,
  ⟨.left,556,0,(-1),false,325,909⟩,
  ⟨.left,557,0,(-1),false,327,951⟩,
  ⟨.left,558,0,(-1),false,329,999⟩,
  ⟨.left,559,0,(-1),false,323,843⟩,
  ⟨.left,560,0,(-1),false,307,855⟩,
  ⟨.left,560,1,(-1),false,303,855⟩,
  ⟨.left,560,2,(-1),false,305,855⟩,
  ⟨.left,560,3,(-1),false,301,855⟩,
  ⟨.left,561,0,(-1),false,311,897⟩,
  ⟨.left,561,1,(-1),false,309,897⟩,
  ⟨.left,562,0,(-1),false,34,981⟩,
  ⟨.left,563,0,(-1),false,28,999⟩,
  ⟨.left,563,1,(-1),false,26,999⟩,
  ⟨.left,563,2,(-1),false,27,999⟩,
  ⟨.left,563,3,(-1),false,25,999⟩,
  ⟨.left,564,0,(-1),false,30,1007⟩,
  ⟨.left,564,1,(-1),false,29,68⟩,
  ⟨.left,565,0,(-1),false,18,969⟩,
  ⟨.left,566,0,(-1),false,17,987⟩,
  ⟨.left,567,0,(-1),false,19,1007⟩,
  ⟨.left,568,0,(-1),false,391,879⟩,
  ⟨.left,569,0,(-1),false,395,921⟩,
  ⟨.left,570,0,(-1),false,403,981⟩,
  ⟨.left,571,0,(-1),false,363,837⟩,
  ⟨.left,571,1,(-1),false,355,837⟩,
  ⟨.left,571,2,(-1),false,359,837⟩,
  ⟨.left,571,3,(-1),false,351,837⟩,
  ⟨.left,572,0,(-1),false,371,867⟩,
  ⟨.left,572,1,(-1),false,367,867⟩,
  ⟨.left,573,0,(-1),false,420,981⟩,
  ⟨.left,574,0,(-1),false,326,909⟩,
  ⟨.left,575,0,(-1),false,328,951⟩,
  ⟨.left,576,0,(-1),false,330,999⟩,
  ⟨.left,577,0,(-1),false,324,843⟩,
  ⟨.left,578,0,(-1),false,308,855⟩,
  ⟨.left,578,1,(-1),false,304,855⟩,
  ⟨.left,578,2,(-1),false,306,855⟩,
  ⟨.left,578,3,(-1),false,302,855⟩,
  ⟨.left,579,0,(-1),false,312,897⟩,
  ⟨.left,579,1,(-1),false,310,897⟩,
  ⟨.left,580,0,(-1),false,407,999⟩,
  ⟨.left,580,1,(-1),false,405,999⟩,
  ⟨.left,581,0,(-1),false,196,969⟩,
  ⟨.left,582,0,(-1),false,195,987⟩,
  ⟨.left,583,0,(-1),false,197,1007⟩,
  ⟨.left,584,0,(-1),false,168,873⟩,
  ⟨.left,585,0,(-1),false,162,903⟩,
  ⟨.left,585,1,(-1),false,160,903⟩,
  ⟨.left,585,2,(-1),false,161,903⟩,
  ⟨.left,585,3,(-1),false,159,903⟩,
  ⟨.left,586,0,(-1),false,164,945⟩,
  ⟨.left,586,1,(-1),false,163,945⟩,
  ⟨.left,587,0,(-1),false,409,1007⟩,
  ⟨.left,587,1,(-1),false,408,68⟩,
  ⟨.left,588,0,(-1),false,13,245⟩,
  ⟨.left,589,0,(-1),false,14,217⟩,
  ⟨.left,590,0,(-1),false,15,217⟩,
  ⟨.left,591,0,(-1),false,10,227⟩,
  ⟨.left,592,0,(-1),false,4,233⟩,
  ⟨.left,592,1,(-1),false,2,233⟩,
  ⟨.left,592,2,(-1),false,3,233⟩,
  ⟨.left,592,3,(-1),false,1,233⟩,
  ⟨.left,593,0,(-1),false,6,239⟩,
  ⟨.left,593,1,(-1),false,5,239⟩,
  ⟨.left,594,0,(-1),false,516,292⟩,
  ⟨.left,594,1,(-1),false,515,298⟩
] : List LowerHistoryRecord) := by rfl

private theorem filter_nonleft (xs : List LowerHistoryRecord)
    (h : ∀ r ∈ xs, r.catalog ≠ .left) (id : Nat) :
    xs.filter (fun r => decide (r.catalog = .left ∧ r.pathId = id)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro r hr
  simpa only [decide_eq_true_eq] using (show ¬ (r.catalog = .left ∧ r.pathId = id) from fun hri => h r hr hri.1)
private theorem left_filter (id : Nat) :
    lowerHistoryRecordsFor (⟨.left,id,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) =
      lowerHistoryRecordsL.toList.filter (fun r => decide (r.catalog = .left ∧ r.pathId = id)) := by
  unfold lowerHistoryRecordsFor lowerHistoryRecords
  simp only [Array.toList_append, List.filter_append]
  rw [filter_nonleft _ nonleft_catalogs.1,
      filter_nonleft _ nonleft_catalogs.2.1,
      filter_nonleft _ nonleft_catalogs.2.2.1,
      filter_nonleft _ nonleft_catalogs.2.2.2]
  simp only [List.append_nil]
private def path6 : LowerHistoryPath := ⟨.left,6,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([1],[]),true)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem records6 : lowerHistoryRecordsFor path6 = [⟨.left,6,0,(-1),false,209,1174⟩] := by
  change lowerHistoryRecordsFor (⟨.left,6,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 6, lowerHistoryRecordsL_list] <;> rfl
private def path7 : LowerHistoryPath := ⟨.left,7,[1],([2],[3]),false,[(([2],[1]),true)],([1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem records7 : lowerHistoryRecordsFor path7 = [⟨.left,7,0,(-1),false,511,1192⟩] := by
  change lowerHistoryRecordsFor (⟨.left,7,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 7, lowerHistoryRecordsL_list] <;> rfl
private def path8 : LowerHistoryPath := ⟨.left,8,[1],([2],[3]),false,[(([2],[1]),false),(([3],[]),true),(([],[1]),false)],([1,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem records8 : lowerHistoryRecordsFor path8 = [⟨.left,8,0,(-1),false,117,1144⟩] := by
  change lowerHistoryRecordsFor (⟨.left,8,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 8, lowerHistoryRecordsL_list] <;> rfl
private def path9 : LowerHistoryPath := ⟨.left,9,[1],([2],[3]),false,[(([2],[1]),false),(([2],[]),true),(([],[1]),false)],([1,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private theorem records9 : lowerHistoryRecordsFor path9 = [⟨.left,9,0,(-1),false,114,1162⟩,⟨.left,9,1,(-1),false,108,1162⟩,⟨.left,9,2,(-1),false,111,1162⟩,⟨.left,9,3,(-1),false,105,1162⟩] := by
  change lowerHistoryRecordsFor (⟨.left,9,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 9, lowerHistoryRecordsL_list] <;> rfl
private def path10 : LowerHistoryPath := ⟨.left,10,[1],([2],[3]),false,[(([2],[1]),false),(([1],[]),true),(([],[1]),false)],([1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private theorem records10 : lowerHistoryRecordsFor path10 = [⟨.left,10,0,(-1),false,126,1180⟩,⟨.left,10,1,(-1),false,123,1180⟩] := by
  change lowerHistoryRecordsFor (⟨.left,10,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 10, lowerHistoryRecordsL_list] <;> rfl
end BatchLookup20

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

namespace BatchLookup20
private theorem bound3 : lowerHistoryBound 3 = sourceBound3 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[2]? = some sourceBound3 := Eq.refl (some sourceBound3)
  exact (BoundCompact16.global_to_chunk1 2 (by decide)).trans hlocal
private theorem bound5 : lowerHistoryBound 5 = sourceBound5 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[4]? = some sourceBound5 := Eq.refl (some sourceBound5)
  exact (BoundCompact16.global_to_chunk1 4 (by decide)).trans hlocal
private theorem bound7 : lowerHistoryBound 7 = sourceBound7 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[6]? = some sourceBound7 := Eq.refl (some sourceBound7)
  exact (BoundCompact16.global_to_chunk1 6 (by decide)).trans hlocal
private theorem bound19 : lowerHistoryBound 19 = sourceBound19 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[18]? = some sourceBound19 := Eq.refl (some sourceBound19)
  exact (BoundCompact16.global_to_chunk1 18 (by decide)).trans hlocal
private theorem bound21 : lowerHistoryBound 21 = sourceBound21 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[20]? = some sourceBound21 := Eq.refl (some sourceBound21)
  exact (BoundCompact16.global_to_chunk1 20 (by decide)).trans hlocal
private theorem bound205 : lowerHistoryBound 205 = sourceBound205 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[4]? = some sourceBound205 := Eq.refl (some sourceBound205)
  exact (BoundCompact16.global_to_chunk2 4 (by decide)).trans hlocal
private theorem bound207 : lowerHistoryBound 207 = sourceBound207 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[6]? = some sourceBound207 := Eq.refl (some sourceBound207)
  exact (BoundCompact16.global_to_chunk2 6 (by decide)).trans hlocal
private theorem bound212 : lowerHistoryBound 212 = sourceBound212 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[11]? = some sourceBound212 := Eq.refl (some sourceBound212)
  exact (BoundCompact16.global_to_chunk2 11 (by decide)).trans hlocal
private theorem bound224 : lowerHistoryBound 224 = sourceBound224 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[23]? = some sourceBound224 := Eq.refl (some sourceBound224)
  exact (BoundCompact16.global_to_chunk2 23 (by decide)).trans hlocal
private theorem bound243 : lowerHistoryBound 243 = sourceBound243 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[42]? = some sourceBound243 := Eq.refl (some sourceBound243)
  exact (BoundCompact16.global_to_chunk2 42 (by decide)).trans hlocal
private theorem bound250 : lowerHistoryBound 250 = sourceBound250 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[49]? = some sourceBound250 := Eq.refl (some sourceBound250)
  exact (BoundCompact16.global_to_chunk2 49 (by decide)).trans hlocal
private theorem bound256 : lowerHistoryBound 256 = sourceBound256 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[55]? = some sourceBound256 := Eq.refl (some sourceBound256)
  exact (BoundCompact16.global_to_chunk2 55 (by decide)).trans hlocal
private theorem bound260 : lowerHistoryBound 260 = sourceBound260 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[59]? = some sourceBound260 := Eq.refl (some sourceBound260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hlocal
private theorem bound265 : lowerHistoryBound 265 = sourceBound265 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[64]? = some sourceBound265 := Eq.refl (some sourceBound265)
  exact (BoundCompact16.global_to_chunk2 64 (by decide)).trans hlocal
private theorem bound275 : lowerHistoryBound 275 = sourceBound275 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[74]? = some sourceBound275 := Eq.refl (some sourceBound275)
  exact (BoundCompact16.global_to_chunk2 74 (by decide)).trans hlocal
private theorem bound277 : lowerHistoryBound 277 = sourceBound277 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[76]? = some sourceBound277 := Eq.refl (some sourceBound277)
  exact (BoundCompact16.global_to_chunk2 76 (by decide)).trans hlocal
private theorem bound371 : lowerHistoryBound 371 = sourceBound371 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[170]? = some sourceBound371 := Eq.refl (some sourceBound371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hlocal
private theorem bound402 : lowerHistoryBound 402 = sourceBound402 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[1]? = some sourceBound402 := Eq.refl (some sourceBound402)
  exact (BoundCompact16.global_to_chunk3 1 (by decide)).trans hlocal
private theorem bound407 : lowerHistoryBound 407 = sourceBound407 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[6]? = some sourceBound407 := Eq.refl (some sourceBound407)
  exact (BoundCompact16.global_to_chunk3 6 (by decide)).trans hlocal
private theorem bound408 : lowerHistoryBound 408 = sourceBound408 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[7]? = some sourceBound408 := Eq.refl (some sourceBound408)
  exact (BoundCompact16.global_to_chunk3 7 (by decide)).trans hlocal
private theorem bound409 : lowerHistoryBound 409 = sourceBound409 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[8]? = some sourceBound409 := Eq.refl (some sourceBound409)
  exact (BoundCompact16.global_to_chunk3 8 (by decide)).trans hlocal
private theorem bound411 : lowerHistoryBound 411 = sourceBound411 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[10]? = some sourceBound411 := Eq.refl (some sourceBound411)
  exact (BoundCompact16.global_to_chunk3 10 (by decide)).trans hlocal
private theorem bound440 : lowerHistoryBound 440 = sourceBound440 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[39]? = some sourceBound440 := Eq.refl (some sourceBound440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hlocal
private theorem bound442 : lowerHistoryBound 442 = sourceBound442 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[41]? = some sourceBound442 := Eq.refl (some sourceBound442)
  exact (BoundCompact16.global_to_chunk3 41 (by decide)).trans hlocal
private theorem bound675 : lowerHistoryBound 675 = sourceBound675 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[74]? = some sourceBound675 := Eq.refl (some sourceBound675)
  exact (BoundCompact16.global_to_chunk4 74 (by decide)).trans hlocal
private theorem bound693 : lowerHistoryBound 693 = sourceBound693 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[92]? = some sourceBound693 := Eq.refl (some sourceBound693)
  exact (BoundCompact16.global_to_chunk4 92 (by decide)).trans hlocal
private theorem bound695 : lowerHistoryBound 695 = sourceBound695 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[94]? = some sourceBound695 := Eq.refl (some sourceBound695)
  exact (BoundCompact16.global_to_chunk4 94 (by decide)).trans hlocal
private theorem bound699 : lowerHistoryBound 699 = sourceBound699 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[98]? = some sourceBound699 := Eq.refl (some sourceBound699)
  exact (BoundCompact16.global_to_chunk4 98 (by decide)).trans hlocal
private theorem bound704 : lowerHistoryBound 704 = sourceBound704 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[103]? = some sourceBound704 := Eq.refl (some sourceBound704)
  exact (BoundCompact16.global_to_chunk4 103 (by decide)).trans hlocal
private theorem bound734 : lowerHistoryBound 734 = sourceBound734 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[133]? = some sourceBound734 := Eq.refl (some sourceBound734)
  exact (BoundCompact16.global_to_chunk4 133 (by decide)).trans hlocal
private theorem bound738 : lowerHistoryBound 738 = sourceBound738 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[137]? = some sourceBound738 := Eq.refl (some sourceBound738)
  exact (BoundCompact16.global_to_chunk4 137 (by decide)).trans hlocal
private theorem bound758 : lowerHistoryBound 758 = sourceBound758 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[157]? = some sourceBound758 := Eq.refl (some sourceBound758)
  exact (BoundCompact16.global_to_chunk4 157 (by decide)).trans hlocal
private theorem bound768 : lowerHistoryBound 768 = sourceBound768 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[167]? = some sourceBound768 := Eq.refl (some sourceBound768)
  exact (BoundCompact16.global_to_chunk4 167 (by decide)).trans hlocal
private theorem bound775 : lowerHistoryBound 775 = sourceBound775 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[174]? = some sourceBound775 := Eq.refl (some sourceBound775)
  exact (BoundCompact16.global_to_chunk4 174 (by decide)).trans hlocal
private theorem bound787 : lowerHistoryBound 787 = sourceBound787 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[186]? = some sourceBound787 := Eq.refl (some sourceBound787)
  exact (BoundCompact16.global_to_chunk4 186 (by decide)).trans hlocal
private theorem bound801 : lowerHistoryBound 801 = sourceBound801 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[0]? = some sourceBound801 := Eq.refl (some sourceBound801)
  exact (BoundCompact16.global_to_chunk5 0 (by decide)).trans hlocal
private theorem bound803 : lowerHistoryBound 803 = sourceBound803 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[2]? = some sourceBound803 := Eq.refl (some sourceBound803)
  exact (BoundCompact16.global_to_chunk5 2 (by decide)).trans hlocal
private theorem bound807 : lowerHistoryBound 807 = sourceBound807 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[6]? = some sourceBound807 := Eq.refl (some sourceBound807)
  exact (BoundCompact16.global_to_chunk5 6 (by decide)).trans hlocal
private theorem bound814 : lowerHistoryBound 814 = sourceBound814 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[13]? = some sourceBound814 := Eq.refl (some sourceBound814)
  exact (BoundCompact16.global_to_chunk5 13 (by decide)).trans hlocal
private theorem bound815 : lowerHistoryBound 815 = sourceBound815 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[14]? = some sourceBound815 := Eq.refl (some sourceBound815)
  exact (BoundCompact16.global_to_chunk5 14 (by decide)).trans hlocal
private theorem bound817 : lowerHistoryBound 817 = sourceBound817 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[16]? = some sourceBound817 := Eq.refl (some sourceBound817)
  exact (BoundCompact16.global_to_chunk5 16 (by decide)).trans hlocal
private theorem bound823 : lowerHistoryBound 823 = sourceBound823 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[22]? = some sourceBound823 := Eq.refl (some sourceBound823)
  exact (BoundCompact16.global_to_chunk5 22 (by decide)).trans hlocal
private theorem bound827 : lowerHistoryBound 827 = sourceBound827 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[26]? = some sourceBound827 := Eq.refl (some sourceBound827)
  exact (BoundCompact16.global_to_chunk5 26 (by decide)).trans hlocal
private theorem bound843 : lowerHistoryBound 843 = sourceBound843 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[42]? = some sourceBound843 := Eq.refl (some sourceBound843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hlocal
private theorem bound856 : lowerHistoryBound 856 = sourceBound856 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[55]? = some sourceBound856 := Eq.refl (some sourceBound856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hlocal
private theorem bound868 : lowerHistoryBound 868 = sourceBound868 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[67]? = some sourceBound868 := Eq.refl (some sourceBound868)
  exact (BoundCompact16.global_to_chunk5 67 (by decide)).trans hlocal
private theorem bound870 : lowerHistoryBound 870 = sourceBound870 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[69]? = some sourceBound870 := Eq.refl (some sourceBound870)
  exact (BoundCompact16.global_to_chunk5 69 (by decide)).trans hlocal
private theorem bound1020 : lowerHistoryBound 1020 = sourceBound1020 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[19]? = some sourceBound1020 := Eq.refl (some sourceBound1020)
  exact (BoundCompact16.global_to_chunk6 19).trans hlocal
private theorem bound1048 : lowerHistoryBound 1048 = sourceBound1048 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[47]? = some sourceBound1048 := Eq.refl (some sourceBound1048)
  exact (BoundCompact16.global_to_chunk6 47).trans hlocal
private theorem bound1065 : lowerHistoryBound 1065 = sourceBound1065 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[64]? = some sourceBound1065 := Eq.refl (some sourceBound1065)
  exact (BoundCompact16.global_to_chunk6 64).trans hlocal
private theorem bound1087 : lowerHistoryBound 1087 = sourceBound1087 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[86]? = some sourceBound1087 := Eq.refl (some sourceBound1087)
  exact (BoundCompact16.global_to_chunk6 86).trans hlocal
private theorem bound1096 : lowerHistoryBound 1096 = sourceBound1096 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[95]? = some sourceBound1096 := Eq.refl (some sourceBound1096)
  exact (BoundCompact16.global_to_chunk6 95).trans hlocal
private theorem bound1113 : lowerHistoryBound 1113 = sourceBound1113 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[112]? = some sourceBound1113 := Eq.refl (some sourceBound1113)
  exact (BoundCompact16.global_to_chunk6 112).trans hlocal
private theorem bound1125 : lowerHistoryBound 1125 = sourceBound1125 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[124]? = some sourceBound1125 := Eq.refl (some sourceBound1125)
  exact (BoundCompact16.global_to_chunk6 124).trans hlocal
private theorem bound1134 : lowerHistoryBound 1134 = sourceBound1134 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[133]? = some sourceBound1134 := Eq.refl (some sourceBound1134)
  exact (BoundCompact16.global_to_chunk6 133).trans hlocal
private theorem bound1144 : lowerHistoryBound 1144 = sourceBound1144 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[143]? = some sourceBound1144 := Eq.refl (some sourceBound1144)
  exact (BoundCompact16.global_to_chunk6 143).trans hlocal
private theorem bound1154 : lowerHistoryBound 1154 = sourceBound1154 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[153]? = some sourceBound1154 := Eq.refl (some sourceBound1154)
  exact (BoundCompact16.global_to_chunk6 153).trans hlocal
private theorem bound1156 : lowerHistoryBound 1156 = sourceBound1156 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[155]? = some sourceBound1156 := Eq.refl (some sourceBound1156)
  exact (BoundCompact16.global_to_chunk6 155).trans hlocal
end BatchLookup20

open Freiman
namespace SourceValues20
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem source6 : lowerHistorySourcePremises BatchLookup20.path6 =
    ([[371,843,260,440,3,856,21,275,442,814,7,807,19,207,699,803,1065]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound814 (congrArg₂ List.cons BatchLookup20.bound7 (congrArg₂ List.cons BatchLookup20.bound807 (congrArg₂ List.cons BatchLookup20.bound19 (congrArg₂ List.cons BatchLookup20.bound207 (congrArg₂ List.cons BatchLookup20.bound699 (congrArg₂ List.cons BatchLookup20.bound803 (congrArg₂ List.cons BatchLookup20.bound1065 (rfl : ([] : List CertBound) = [])))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo20_6.source.trans hb.symm
private theorem length6 : BatchLookup20.path6.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path6).length := by
  exact (congrArg List.length source6).symm
private theorem source7 : lowerHistorySourcePremises BatchLookup20.path7 =
    ([[371,843,260,440,3,856,21,275,442,277,827,870,1156]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound277 (congrArg₂ List.cons BatchLookup20.bound827 (congrArg₂ List.cons BatchLookup20.bound870 (congrArg₂ List.cons BatchLookup20.bound1156 (rfl : ([] : List CertBound) = [])))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo20_7.source.trans hb.symm
private theorem length7 : BatchLookup20.path7.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path7).length := by
  exact (congrArg List.length source7).symm
private theorem source8 : lowerHistorySourcePremises BatchLookup20.path8 =
    ([[371,843,260,440,3,856,21,275,442,817,5,1125,408,695,1096,407,675,758,1020,212]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound817 (congrArg₂ List.cons BatchLookup20.bound5 (congrArg₂ List.cons BatchLookup20.bound1125 (congrArg₂ List.cons BatchLookup20.bound408 (congrArg₂ List.cons BatchLookup20.bound695 (congrArg₂ List.cons BatchLookup20.bound1096 (congrArg₂ List.cons BatchLookup20.bound407 (congrArg₂ List.cons BatchLookup20.bound675 (congrArg₂ List.cons BatchLookup20.bound758 (congrArg₂ List.cons BatchLookup20.bound1020 (congrArg₂ List.cons BatchLookup20.bound212 (rfl : ([] : List CertBound) = []))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo20_8.source.trans hb.symm
private theorem length8 : BatchLookup20.path8.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path8).length := by
  exact (congrArg List.length source8).symm
private theorem source9 : lowerHistorySourcePremises BatchLookup20.path9 =
    ([[371,843,260,440,3,856,21,275,442,817,5,1125,411,734,1113,402,693,787,1048,205],[371,843,260,440,3,856,21,275,442,817,5,1125,411,734,243,775,704,1134,402,693,787,1048,205],[371,843,260,440,3,856,21,275,442,817,5,250,868,411,734,1113,402,693,787,1048,205],[371,843,260,440,3,856,21,275,442,817,5,250,868,411,734,243,775,704,1134,402,693,787,1048,205]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound817 (congrArg₂ List.cons BatchLookup20.bound5 (congrArg₂ List.cons BatchLookup20.bound1125 (congrArg₂ List.cons BatchLookup20.bound411 (congrArg₂ List.cons BatchLookup20.bound734 (congrArg₂ List.cons BatchLookup20.bound1113 (congrArg₂ List.cons BatchLookup20.bound402 (congrArg₂ List.cons BatchLookup20.bound693 (congrArg₂ List.cons BatchLookup20.bound787 (congrArg₂ List.cons BatchLookup20.bound1048 (congrArg₂ List.cons BatchLookup20.bound205 (rfl : ([] : List CertBound) = []))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound817 (congrArg₂ List.cons BatchLookup20.bound5 (congrArg₂ List.cons BatchLookup20.bound1125 (congrArg₂ List.cons BatchLookup20.bound411 (congrArg₂ List.cons BatchLookup20.bound734 (congrArg₂ List.cons BatchLookup20.bound243 (congrArg₂ List.cons BatchLookup20.bound775 (congrArg₂ List.cons BatchLookup20.bound704 (congrArg₂ List.cons BatchLookup20.bound1134 (congrArg₂ List.cons BatchLookup20.bound402 (congrArg₂ List.cons BatchLookup20.bound693 (congrArg₂ List.cons BatchLookup20.bound787 (congrArg₂ List.cons BatchLookup20.bound1048 (congrArg₂ List.cons BatchLookup20.bound205 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound817 (congrArg₂ List.cons BatchLookup20.bound5 (congrArg₂ List.cons BatchLookup20.bound250 (congrArg₂ List.cons BatchLookup20.bound868 (congrArg₂ List.cons BatchLookup20.bound411 (congrArg₂ List.cons BatchLookup20.bound734 (congrArg₂ List.cons BatchLookup20.bound1113 (congrArg₂ List.cons BatchLookup20.bound402 (congrArg₂ List.cons BatchLookup20.bound693 (congrArg₂ List.cons BatchLookup20.bound787 (congrArg₂ List.cons BatchLookup20.bound1048 (congrArg₂ List.cons BatchLookup20.bound205 (rfl : ([] : List CertBound) = [])))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound817 (congrArg₂ List.cons BatchLookup20.bound5 (congrArg₂ List.cons BatchLookup20.bound250 (congrArg₂ List.cons BatchLookup20.bound868 (congrArg₂ List.cons BatchLookup20.bound411 (congrArg₂ List.cons BatchLookup20.bound734 (congrArg₂ List.cons BatchLookup20.bound243 (congrArg₂ List.cons BatchLookup20.bound775 (congrArg₂ List.cons BatchLookup20.bound704 (congrArg₂ List.cons BatchLookup20.bound1134 (congrArg₂ List.cons BatchLookup20.bound402 (congrArg₂ List.cons BatchLookup20.bound693 (congrArg₂ List.cons BatchLookup20.bound787 (congrArg₂ List.cons BatchLookup20.bound1048 (congrArg₂ List.cons BatchLookup20.bound205 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))))
  exact SourceMemo20_9.source.trans hb.symm
private theorem length9 : BatchLookup20.path9.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path9).length := by
  exact (congrArg List.length source9).symm
private theorem source10 : lowerHistorySourcePremises BatchLookup20.path10 =
    ([[371,843,260,440,3,856,21,275,442,817,5,256,801,1144,409,738,823,1087,224],[371,843,260,440,3,856,21,275,442,817,5,256,801,265,815,768,1154,409,738,823,1087,224]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound817 (congrArg₂ List.cons BatchLookup20.bound5 (congrArg₂ List.cons BatchLookup20.bound256 (congrArg₂ List.cons BatchLookup20.bound801 (congrArg₂ List.cons BatchLookup20.bound1144 (congrArg₂ List.cons BatchLookup20.bound409 (congrArg₂ List.cons BatchLookup20.bound738 (congrArg₂ List.cons BatchLookup20.bound823 (congrArg₂ List.cons BatchLookup20.bound1087 (congrArg₂ List.cons BatchLookup20.bound224 (rfl : ([] : List CertBound) = [])))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound817 (congrArg₂ List.cons BatchLookup20.bound5 (congrArg₂ List.cons BatchLookup20.bound256 (congrArg₂ List.cons BatchLookup20.bound801 (congrArg₂ List.cons BatchLookup20.bound265 (congrArg₂ List.cons BatchLookup20.bound815 (congrArg₂ List.cons BatchLookup20.bound768 (congrArg₂ List.cons BatchLookup20.bound1154 (congrArg₂ List.cons BatchLookup20.bound409 (congrArg₂ List.cons BatchLookup20.bound738 (congrArg₂ List.cons BatchLookup20.bound823 (congrArg₂ List.cons BatchLookup20.bound1087 (congrArg₂ List.cons BatchLookup20.bound224 (rfl : ([] : List CertBound) = []))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))
  exact SourceMemo20_10.source.trans hb.symm
private theorem length10 : BatchLookup20.path10.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path10).length := by
  exact (congrArg List.length source10).symm
end SourceValues20


namespace PremiseCompact50

variable {α : Type} (a b c d e f : Array α)
  (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200)
  (hd : d.size = 200) (he : e.size = 200)
include ha hb hc hd he

private theorem lookup_chunk1 (i : ℕ) (hi : i < 200) :
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

private theorem lookup_chunk2 (i : ℕ) (hi : i < 200) :
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

private theorem lookup_chunk3 (i : ℕ) (hi : i < 200) :
    (a ++ b ++ c ++ d ++ e ++ f)[400 + i]? = c[i]? := by
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

end PremiseCompact50

open Freiman
namespace BatchLookup20
set_option maxRecDepth 30000
private theorem size01 : lowerHistoryPremises01.size = 200 := by rfl
private theorem size02 : lowerHistoryPremises02.size = 200 := by rfl
private theorem size03 : lowerHistoryPremises03.size = 200 := by rfl
private theorem size04 : lowerHistoryPremises04.size = 200 := by rfl
private theorem size05 : lowerHistoryPremises05.size = 200 := by rfl
private theorem premise105 : lowerHistoryPremises[104]? = some ([3,5,21,205,243,250,260,275,371,402,411,440,442,693,704,734,775,787,817,843,856,868,1048,1134] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 104 = 0+104 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 104 (by decide)]
  rfl
private theorem premise108 : lowerHistoryPremises[107]? = some ([3,5,21,205,243,260,275,371,402,411,440,442,693,704,734,775,787,817,843,856,1048,1125,1134] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 107 = 0+107 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 107 (by decide)]
  rfl
private theorem premise111 : lowerHistoryPremises[110]? = some ([3,5,21,205,250,260,275,371,402,411,440,442,693,734,787,817,843,856,868,1048,1113] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 110 = 0+110 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 110 (by decide)]
  rfl
private theorem premise114 : lowerHistoryPremises[113]? = some ([3,5,21,205,260,275,371,402,411,440,442,693,734,787,817,843,856,1048,1113,1125] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 113 = 0+113 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 113 (by decide)]
  rfl
private theorem premise117 : lowerHistoryPremises[116]? = some ([3,5,21,212,260,275,371,407,408,440,442,675,695,758,817,843,856,1020,1096,1125] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 116 = 0+116 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 116 (by decide)]
  rfl
private theorem premise123 : lowerHistoryPremises[122]? = some ([3,5,21,224,256,260,265,275,371,409,440,442,738,768,801,815,817,823,843,856,1087,1154] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 122 = 0+122 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 122 (by decide)]
  rfl
private theorem premise126 : lowerHistoryPremises[125]? = some ([3,5,21,224,256,260,275,371,409,440,442,738,801,817,823,843,856,1087,1144] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 125 = 0+125 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 125 (by decide)]
  rfl
private theorem premise209 : lowerHistoryPremises[208]? = some ([3,7,19,21,207,260,275,371,440,442,699,803,807,814,843,856,1065] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 208 = 200+8 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 8 (by decide)]
  rfl
private theorem premise511 : lowerHistoryPremises[510]? = some ([3,21,260,275,277,371,440,442,827,843,856,870,1156] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 510 = 400+110 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 110 (by decide)]
  rfl
end BatchLookup20

open Freiman
namespace BatchFacts15

end BatchFacts15

open Freiman BatchFacts15
namespace ExtrasMemo15
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
end ExtrasMemo15

open Freiman
namespace ExtraValues20
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
end ExtraValues20

open Freiman
namespace BatchCoverage15

private def coverageCheck (p : LowerHistoryPath) (rs : List LowerHistoryRecord) (ai : ℕ) : Bool :=
  rs.any (fun r => decide (r.alternative = ai ∧ r.endpointBranch < 0)) ||
    (decide (p.catalog ≠ .initial ∧ p.row ≠ 4) &&
      ((lowerHistoryEndpointComparisons p).zipIdx.all fun (cg,bi) =>
        decide (cg.2 = .automatic) || rs.any fun r =>
          decide (r.alternative = ai ∧ r.endpointBranch = (bi : ℤ) ∧ r.survivor = false)))

private theorem coverage_sound (p : LowerHistoryPath) (rs : List LowerHistoryRecord)
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

open Freiman BatchLookup20 BatchCoverage15
namespace BatchCoverageAll20
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000

private theorem coverage6 : (List.range path6.alternatives).all (coverageCheck path6 ([⟨.left,6,0,(-1),false,209,1174⟩] : List LowerHistoryRecord)) = true := by decide +kernel


private theorem coverage7 : (List.range path7.alternatives).all (coverageCheck path7 ([⟨.left,7,0,(-1),false,511,1192⟩] : List LowerHistoryRecord)) = true := by decide +kernel


private theorem coverage8 : (List.range path8.alternatives).all (coverageCheck path8 ([⟨.left,8,0,(-1),false,117,1144⟩] : List LowerHistoryRecord)) = true := by decide +kernel


private theorem coverage9 : (List.range path9.alternatives).all (coverageCheck path9 ([⟨.left,9,0,(-1),false,114,1162⟩,⟨.left,9,1,(-1),false,108,1162⟩,⟨.left,9,2,(-1),false,111,1162⟩,⟨.left,9,3,(-1),false,105,1162⟩] : List LowerHistoryRecord)) = true := by decide +kernel


private theorem coverage10 : (List.range path10.alternatives).all (coverageCheck path10 ([⟨.left,10,0,(-1),false,126,1180⟩,⟨.left,10,1,(-1),false,123,1180⟩] : List LowerHistoryRecord)) = true := by decide +kernel


end BatchCoverageAll20

open Freiman BatchLookup20
namespace PathLookup20
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem append5_get {α : Type} (a b c d e : Array α) (i : Nat)
    (h : i < a.size) : ((((a ++ b) ++ c) ++ d) ++ e)[i]? = a[i]? := by
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega)]
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega)]
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega)]
  rw [Array.getElem?_append_left h]
private theorem sizeL : lowerHistoryPathsL.size = 594 := by rfl
private theorem first_lookup (i : Nat) (h : i < 50) :
    lowerHistoryPaths[i]? = lowerHistoryPathsL[i]? := by
  apply append5_get
  rw [sizeL]
  omega
private theorem path6_lookup : lowerHistoryPaths[5]? = some path6 := by
  rw [first_lookup 5 (by decide)]
  rfl
private theorem path7_lookup : lowerHistoryPaths[6]? = some path7 := by
  rw [first_lookup 6 (by decide)]
  rfl
private theorem path8_lookup : lowerHistoryPaths[7]? = some path8 := by
  rw [first_lookup 7 (by decide)]
  rfl
private theorem path9_lookup : lowerHistoryPaths[8]? = some path9 := by
  rw [first_lookup 8 (by decide)]
  rfl
private theorem path10_lookup : lowerHistoryPaths[9]? = some path10 := by
  rw [first_lookup 9 (by decide)]
  rfl
end PathLookup20

-- Reduce the global witness array structurally, then
-- let the kernel inspect only the selected entry of its 200-element chunk.
open Freiman
namespace WitnessCompact16
set_option maxRecDepth 30000

private def witnessShape (w : CertWitness) : CertBound × CertBound × CertRectangle :=
  (w.lowerBound, w.upperBound, w.rectangle)

private def emptyWitness : CertWitness :=
  ⟨lowerHistoryBound 0, lowerHistoryBound 0, ⟨0,1,0,1⟩,
    fun _ _ => ⟨0,0,0,0⟩, fun _ _ => 0⟩

private theorem lowerHistoryWitness_def (id : ℕ) :
    lowerHistoryWitness id =
      (lowerHistoryWitnesses[id - 1]?).getD emptyWitness := by
  rfl

private theorem projections_of_shape (w : CertWitness) (l u : CertBound)
    (r : CertRectangle) (h : witnessShape w = (l, u, r)) :
    w.lowerBound = l ∧ w.upperBound = u ∧ w.rectangle = r := by
  simpa only [witnessShape, Prod.mk.injEq] using h

private theorem shape_of_global_option (id : ℕ)
    (target : CertBound × CertBound × CertRectangle)
    (h : (lowerHistoryWitnesses[id - 1]?).map witnessShape = some target) :
    witnessShape (lowerHistoryWitness id) = target := by
  have hs : witnessShape ((lowerHistoryWitnesses[id - 1]?).getD emptyWitness) =
      target := by
    cases ho : lowerHistoryWitnesses[id - 1]? <;> simp_all
  exact (congrArg witnessShape (lowerHistoryWitness_def id)).trans hs

private theorem projection_of_global_option (id : ℕ)
    (l u : CertBound) (r : CertRectangle)
    (h : (lowerHistoryWitnesses[id - 1]?).map witnessShape = some (l, u, r)) :
    (lowerHistoryWitness id).lowerBound = l ∧
    (lowerHistoryWitness id).upperBound = u ∧
    (lowerHistoryWitness id).rectangle = r := by
  exact projections_of_shape _ _ _ _ (shape_of_global_option id (l, u, r) h)

private theorem size01 : lowerHistoryWitnesses01.size = 200 := by rfl
private theorem size02 : lowerHistoryWitnesses02.size = 200 := by rfl
private theorem size03 : lowerHistoryWitnesses03.size = 200 := by rfl
private theorem size04 : lowerHistoryWitnesses04.size = 200 := by rfl
private theorem size05 : lowerHistoryWitnesses05.size = 200 := by rfl

private theorem global_to_chunk6 (i : ℕ) :
    lowerHistoryWitnesses[1000 + i]? = lowerHistoryWitnesses06[i]? := by
  unfold lowerHistoryWitnesses
  rw [Array.getElem?_append_right (xs := lowerHistoryWitnesses01 ++ lowerHistoryWitnesses02 ++ lowerHistoryWitnesses03 ++ lowerHistoryWitnesses04 ++ lowerHistoryWitnesses05)
    (by simp only [Array.size_append, size01, size02, size03, size04, size05]; omega)]
  simp only [Array.size_append, size01, size02, size03, size04, size05]
  exact congrArg (fun j => lowerHistoryWitnesses06[j]?) (by omega)

end WitnessCompact16

namespace WitnessLookup20
private theorem witness1144_projection :
    (lowerHistoryWitness 1144).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1144).upperBound = lowerHistoryBound 1020 ∧
    (lowerHistoryWitness 1144).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[143]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1020, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1020, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 143)).trans hl
private theorem witness1162_projection :
    (lowerHistoryWitness 1162).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1162).upperBound = lowerHistoryBound 1048 ∧
    (lowerHistoryWitness 1162).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[161]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1048, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1048, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 161)).trans hl
private theorem witness1174_projection :
    (lowerHistoryWitness 1174).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1174).upperBound = lowerHistoryBound 1065 ∧
    (lowerHistoryWitness 1174).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[173]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1065, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1065, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 173)).trans hl
private theorem witness1180_projection :
    (lowerHistoryWitness 1180).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1180).upperBound = lowerHistoryBound 1087 ∧
    (lowerHistoryWitness 1180).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[179]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1087, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1087, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 179)).trans hl
private theorem witness1192_projection :
    (lowerHistoryWitness 1192).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1192).upperBound = lowerHistoryBound 1156 ∧
    (lowerHistoryWitness 1192).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[191]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1156, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1156, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 191)).trans hl
end WitnessLookup20

open Freiman
namespace BindingIds19
set_option Elab.async false
set_option linter.all false
set_option maxHeartbeats 0
set_option maxRecDepth 30000

private def extras (p : LowerHistoryPath) (branch : Nat) : List CertBound :=
  let comp := (lowerHistoryEndpointComparisons p)[branch]?.getD ([],.automatic)
  comp.1 ++ (match comp.2 with | .bound b => [lowerHistoryComplement b] | _ => [])

private def residualIds (src ext : List (List Nat)) (r : LowerHistoryRecord) : List Nat :=
  if r.endpointBranch < 0 then src[r.alternative]?.getD []
  else src[r.alternative]?.getD [] ++ ext[r.endpointBranch.toNat]?.getD []

private instance survivorDecidable (p : LowerHistoryPath) : Decidable (lowerHistorySurvivor p) := by
  unfold lowerHistorySurvivor
  infer_instance

private def recordCheck (p : LowerHistoryPath) (src ext : List (List Nat))
    (wids : Nat → Nat × Nat) (preIDs : Nat → List Nat) (np nw : Nat) (r : LowerHistoryRecord) : Bool :=
  if r.survivor then decide (lowerHistorySurvivor p ∧ r.alternative = 0) else
  decide (0 < r.premiseId ∧ r.premiseId ≤ np ∧
    0 < r.witnessId ∧ r.witnessId ≤ nw ∧
    (r.endpointBranch < 0 ∨ r.endpointBranch.toNat < ext.length) ∧
    (preIDs r.premiseId).toFinset = (residualIds src ext r).toFinset ∧
    (wids r.witnessId).1 ∈ preIDs r.premiseId ∧
    (wids r.witnessId).2 ∈ preIDs r.premiseId)

private theorem map_getD (xs : List (List Nat)) (i : Nat) :
    ((xs.map (List.map lowerHistoryBound))[i]?).getD [] =
      (xs[i]?.getD []).map lowerHistoryBound := by
  cases h : xs[i]? <;> simp [List.getElem?_map, h]

private theorem mapped_finset_congr (a b : List Nat) (h : a.toFinset = b.toFinset) :
    (a.map lowerHistoryBound).toFinset = (b.map lowerHistoryBound).toFinset := by
  have hm : ∀ x, x ∈ a ↔ x ∈ b := by
    intro x
    simpa only [List.mem_toFinset] using
      (Iff.of_eq (congrArg (fun s : Finset Nat => x ∈ s) h))
  ext x
  simp only [List.mem_toFinset, List.mem_map, hm]

private theorem residual_values (p : LowerHistoryPath) (src ext : List (List Nat))
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

private theorem recordCheck_sound (p : LowerHistoryPath) (src ext : List (List Nat))
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

private theorem pathBinding_from_ids (p : LowerHistoryPath) (src ext : List (List Nat))
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

open Freiman BatchLookup20 BindingIds19
namespace BatchIdSolution0
set_option maxRecDepth 30000
set_option maxHeartbeats 0
private theorem premise_size : lowerHistoryPremises.size = 1025 := by
  simp only [lowerHistoryPremises, Array.size_append]
  rfl
private theorem witness_size : lowerHistoryWitnesses.size = 1194 := by
  simp only [lowerHistoryWitnesses, Array.size_append]
  rfl
private def wids : Nat → Nat × Nat
  | 36 => (285,836)
  | 40 => (285,879)
  | 44 => (285,891)
  | 50 => (285,1139)
  | 66 => (286,1117)
  | 119 => (287,969)
  | 125 => (287,990)
  | 131 => (287,1026)
  | 137 => (287,1064)
  | 143 => (287,1086)
  | 149 => (287,1117)
  | 266 => (295,836)
  | 270 => (295,883)
  | 274 => (295,894)
  | 280 => (295,1139)
  | 306 => (429,881)
  | 566 => (439,836)
  | 570 => (439,881)
  | 574 => (439,892)
  | 580 => (439,1139)
  | 794 => (440,836)
  | 799 => (440,892)
  | 817 => (440,929)
  | 823 => (440,942)
  | 829 => (440,943)
  | 847 => (440,957)
  | 859 => (440,965)
  | 871 => (440,969)
  | 883 => (440,984)
  | 889 => (440,986)
  | 901 => (440,990)
  | 913 => (440,1016)
  | 925 => (440,1020)
  | 931 => (440,1021)
  | 937 => (440,1022)
  | 943 => (440,1026)
  | 955 => (440,1048)
  | 961 => (440,1051)
  | 967 => (440,1064)
  | 973 => (440,1065)
  | 979 => (440,1071)
  | 985 => (440,1086)
  | 991 => (440,1087)
  | 997 => (440,1093)
  | 1005 => (440,1117)
  | 1020 => (440,1139)
  | 1024 => (440,1142)
  | 1048 => (440,1153)
  | 1132 => (442,984)
  | 1138 => (442,1016)
  | 1144 => (442,1020)
  | 1150 => (442,1021)
  | 1156 => (442,1022)
  | 1162 => (442,1048)
  | 1168 => (442,1051)
  | 1174 => (442,1065)
  | 1180 => (442,1087)
  | 1186 => (442,1142)
  | 1192 => (442,1156)
  | _ => (0,0)
private def preIDs : Nat → List Nat
  | 22 => [2,3,6,21,234,260,282,371,413,440,689,802,810,825,837,843,851,856,1064,1120,1129,1148]
  | 37 => [2,3,21,236,260,266,274,282,371,414,418,440,747,763,779,813,829,837,843,851,856,878,1093,1155]
  | 38 => [2,3,21,236,260,266,282,371,414,418,440,747,763,779,813,829,837,843,851,856,1093,1152,1155]
  | 39 => [2,3,21,236,260,274,282,371,414,418,440,747,779,829,837,843,851,856,878,1093,1145]
  | 40 => [2,3,21,236,260,282,371,414,418,440,747,779,829,837,843,851,856,1093,1145,1152]
  | 41 => [2,3,21,244,260,270,282,286,371,417,440,782,805,831,837,843,846,851,853,856,1117,1173]
  | 42 => [2,3,21,244,260,270,282,371,417,440,782,831,837,843,851,853,856,1117,1164]
  | 55 => [2,3,21,260,262,282,371,423,426,440,736,752,809,837,843,851,856,1071,1132,1152]
  | 92 => [3,5,8,21,201,260,275,371,400,420,440,664,780,781,790,791,817,843,856,876,1051,1122]
  | 93 => [3,5,8,21,201,260,275,371,400,440,442,664,781,790,791,817,843,856,1051,1122]
  | 94 => [3,5,8,21,201,260,371,400,420,440,664,780,781,790,791,817,843,856,1051,1122,1153]
  | 95 => [3,5,8,21,224,260,275,371,420,440,738,780,781,817,823,843,856,876,1087]
  | 96 => [3,5,8,21,224,260,275,371,440,442,738,781,817,823,843,856,1087]
  | 97 => [3,5,8,21,224,260,371,420,440,738,780,781,817,823,843,856,1087,1153]
  | 98 => [3,5,8,21,232,260,275,371,412,420,440,631,764,780,781,791,817,843,856,876,1021,1091,1103,1122]
  | 99 => [3,5,8,21,232,260,275,371,412,440,442,631,764,781,791,817,843,856,1021,1091,1103,1122]
  | 100 => [3,5,8,21,232,260,371,412,420,440,631,764,780,781,791,817,843,856,1021,1091,1103,1122,1153]
  | 104 => [3,5,21,205,243,250,260,275,371,402,411,420,440,693,704,734,775,780,787,817,843,856,868,876,1048,1134]
  | 105 => [3,5,21,205,243,250,260,275,371,402,411,440,442,693,704,734,775,787,817,843,856,868,1048,1134]
  | 106 => [3,5,21,205,243,250,260,371,402,411,420,440,693,704,734,775,780,787,817,843,856,868,1048,1134,1153]
  | 107 => [3,5,21,205,243,260,275,371,402,411,420,440,693,704,734,775,780,787,817,843,856,876,1048,1125,1134]
  | 108 => [3,5,21,205,243,260,275,371,402,411,440,442,693,704,734,775,787,817,843,856,1048,1125,1134]
  | 109 => [3,5,21,205,243,260,371,402,411,420,440,693,704,734,775,780,787,817,843,856,1048,1125,1134,1153]
  | 110 => [3,5,21,205,250,260,275,371,402,411,420,440,693,734,780,787,817,843,856,868,876,1048,1113]
  | 111 => [3,5,21,205,250,260,275,371,402,411,440,442,693,734,787,817,843,856,868,1048,1113]
  | 112 => [3,5,21,205,250,260,371,402,411,420,440,693,734,780,787,817,843,856,868,1048,1113,1153]
  | 113 => [3,5,21,205,260,275,371,402,411,420,440,693,734,780,787,817,843,856,876,1048,1113,1125]
  | 114 => [3,5,21,205,260,275,371,402,411,440,442,693,734,787,817,843,856,1048,1113,1125]
  | 115 => [3,5,21,205,260,371,402,411,420,440,693,734,780,787,817,843,856,1048,1113,1125,1153]
  | 116 => [3,5,21,212,260,275,371,407,408,420,440,675,695,758,780,817,843,856,876,1020,1096,1125]
  | 117 => [3,5,21,212,260,275,371,407,408,440,442,675,695,758,817,843,856,1020,1096,1125]
  | 118 => [3,5,21,212,260,371,407,408,420,440,675,695,758,780,817,843,856,1020,1096,1125,1153]
  | 122 => [3,5,21,224,256,260,265,275,371,409,420,440,738,768,780,801,815,817,823,843,856,876,1087,1154]
  | 123 => [3,5,21,224,256,260,265,275,371,409,440,442,738,768,801,815,817,823,843,856,1087,1154]
  | 124 => [3,5,21,224,256,260,265,371,409,420,440,738,768,780,801,815,817,823,843,856,1087,1153,1154]
  | 125 => [3,5,21,224,256,260,275,371,409,420,440,738,780,801,817,823,843,856,876,1087,1144]
  | 126 => [3,5,21,224,256,260,275,371,409,440,442,738,801,817,823,843,856,1087,1144]
  | 127 => [3,5,21,224,256,260,371,409,420,440,738,780,801,817,823,843,856,1087,1144,1153]
  | 171 => [3,6,13,21,159,215,220,260,282,287,371,387,396,419,440,602,616,653,706,725,769,784,810,811,837,843,852,856,869,990,1082,1181]
  | 172 => [3,6,13,21,159,215,220,260,282,371,387,396,419,440,602,616,653,706,725,769,784,810,837,843,856,869,990,1082,1165]
  | 173 => [3,6,13,21,159,215,260,282,287,371,387,396,419,440,602,616,653,706,725,769,784,810,811,837,843,852,856,990,1078,1082,1181]
  | 174 => [3,6,13,21,159,215,260,282,371,387,396,419,440,602,616,653,706,725,769,784,810,837,843,856,990,1078,1082,1165]
  | 175 => [3,6,13,21,159,220,260,282,287,371,387,396,419,440,602,653,725,769,784,810,811,837,843,852,856,869,990,1073,1181]
  | 176 => [3,6,13,21,159,220,260,282,371,387,396,419,440,602,653,725,769,784,810,837,843,856,869,990,1073,1165]
  | 177 => [3,6,13,21,159,260,282,287,371,387,396,419,440,602,653,725,769,784,810,811,837,843,852,856,990,1073,1078,1181]
  | 178 => [3,6,13,21,159,260,282,371,387,396,419,440,602,653,725,769,784,810,837,843,856,990,1073,1078,1165]
  | 179 => [3,6,13,21,179,219,237,260,282,287,371,394,419,440,657,687,728,761,769,771,784,810,811,837,843,852,856,1026,1114,1181]
  | 180 => [3,6,13,21,179,219,237,260,282,371,394,419,440,657,687,728,761,769,771,784,810,837,843,856,1026,1114,1165]
  | 181 => [3,6,13,21,179,219,260,282,287,371,394,419,440,657,728,769,771,784,810,811,837,843,852,856,1026,1105,1181]
  | 182 => [3,6,13,21,179,219,260,282,371,394,419,440,657,728,769,771,784,810,837,843,856,1026,1105,1165]
  | 189 => [3,6,13,21,196,260,282,287,371,397,403,419,440,590,609,691,769,784,810,811,837,843,852,856,969,1039,1078,1181]
  | 190 => [3,6,13,21,196,260,282,371,397,403,419,440,590,609,691,769,784,810,837,843,856,969,1039,1078,1165]
  | 199 => [3,6,21,225,260,282,287,371,410,419,440,724,784,810,811,822,825,837,843,852,856,1086,1148,1181]
  | 200 => [3,6,21,225,260,282,371,410,419,440,724,784,810,822,825,837,843,856,1086,1148,1165]
  | 201 => [3,6,21,234,260,282,287,371,413,419,440,689,784,802,810,811,825,837,843,852,856,1064,1120,1129,1148,1181]
  | 202 => [3,6,21,234,260,282,371,413,419,440,689,784,802,810,825,837,843,856,1064,1120,1129,1148,1165]
  | 203 => [3,6,21,244,260,282,287,371,419,440,782,784,810,811,837,843,852,853,856,1117,1181]
  | 204 => [3,6,21,244,260,282,371,419,440,782,784,810,837,843,853,856,1117,1165]
  | 207 => [3,7,19,21,178,260,275,371,393,440,442,621,766,767,807,814,843,856,1022,1106]
  | 208 => [3,7,19,21,178,260,371,393,425,440,621,751,766,767,807,814,843,856,1022,1106,1153]
  | 209 => [3,7,19,21,207,260,275,371,440,442,699,803,807,814,843,856,1065]
  | 210 => [3,7,19,21,207,260,371,425,440,699,751,803,807,814,843,856,1065,1153]
  | 213 => [3,7,21,176,230,239,260,275,371,391,406,440,442,646,658,697,740,754,814,843,850,856,1016,1111]
  | 214 => [3,7,21,176,230,239,260,371,391,406,425,440,646,658,697,740,751,754,814,843,850,856,1016,1111,1153]
  | 215 => [3,7,21,176,230,260,275,371,391,406,440,442,646,658,697,740,754,814,843,856,1016,1107,1111]
  | 216 => [3,7,21,176,230,260,371,391,406,425,440,646,658,697,740,751,754,814,843,856,1016,1107,1111,1153]
  | 217 => [3,7,21,176,239,260,275,371,391,406,440,442,646,697,754,814,843,850,856,1016,1094]
  | 218 => [3,7,21,176,239,260,371,391,406,425,440,646,697,751,754,814,843,850,856,1016,1094,1153]
  | 219 => [3,7,21,176,260,275,371,391,406,440,442,646,697,754,814,843,856,1016,1094,1107]
  | 220 => [3,7,21,176,260,371,391,406,425,440,646,697,751,754,814,843,856,1016,1094,1107,1153]
  | 221 => [3,7,21,177,260,275,371,392,399,440,442,627,650,718,814,843,856,984,1067,1107]
  | 222 => [3,7,21,177,260,371,392,399,425,440,627,650,718,751,814,843,856,984,1067,1107,1153]
  | 225 => [3,7,21,207,251,260,264,275,371,404,440,442,699,729,788,793,803,814,843,856,1065,1143]
  | 226 => [3,7,21,207,251,260,264,371,404,425,440,699,729,751,788,793,803,814,843,856,1065,1143,1153]
  | 227 => [3,7,21,207,260,264,275,371,404,440,442,699,788,803,814,843,856,1065,1126]
  | 228 => [3,7,21,207,260,264,371,404,425,440,699,751,788,803,814,843,856,1065,1126,1153]
  | 237 => [3,8,21,34,136,180,191,260,267,275,371,376,385,416,420,440,545,560,591,649,663,711,746,772,780,781,821,843,845,856,876,957,1046,1157]
  | 238 => [3,8,21,34,136,180,191,260,267,371,376,385,416,420,440,545,560,591,649,663,711,746,772,780,781,821,843,845,856,957,1046,1153,1157]
  | 239 => [3,8,21,34,136,180,191,260,275,371,376,385,416,420,440,545,560,591,649,663,711,746,780,781,843,845,856,876,957,1046,1146]
  | 240 => [3,8,21,34,136,180,191,260,371,376,385,416,420,440,545,560,591,649,663,711,746,780,781,843,845,856,957,1046,1146,1153]
  | 241 => [3,8,21,34,136,180,260,267,275,371,376,385,416,420,440,545,560,591,649,663,711,746,772,780,781,821,843,856,876,957,1037,1046,1157]
  | 242 => [3,8,21,34,136,180,260,267,371,376,385,416,420,440,545,560,591,649,663,711,746,772,780,781,821,843,856,957,1037,1046,1153,1157]
  | 243 => [3,8,21,34,136,180,260,275,371,376,385,416,420,440,545,560,591,649,663,711,746,780,781,843,856,876,957,1037,1046,1146]
  | 244 => [3,8,21,34,136,180,260,371,376,385,416,420,440,545,560,591,649,663,711,746,780,781,843,856,957,1037,1046,1146,1153]
  | 245 => [3,8,21,34,136,191,260,267,275,371,376,385,416,420,440,545,591,663,711,746,772,780,781,821,843,845,856,876,957,1025,1157]
  | 246 => [3,8,21,34,136,191,260,267,371,376,385,416,420,440,545,591,663,711,746,772,780,781,821,843,845,856,957,1025,1153,1157]
  | 247 => [3,8,21,34,136,191,260,275,371,376,385,416,420,440,545,591,663,711,746,780,781,843,845,856,876,957,1025,1146]
  | 248 => [3,8,21,34,136,191,260,371,376,385,416,420,440,545,591,663,711,746,780,781,843,845,856,957,1025,1146,1153]
  | 249 => [3,8,21,34,136,260,267,275,371,376,385,416,420,440,545,591,663,711,746,772,780,781,821,843,856,876,957,1025,1037,1157]
  | 250 => [3,8,21,34,136,260,267,371,376,385,416,420,440,545,591,663,711,746,772,780,781,821,843,856,957,1025,1037,1153,1157]
  | 251 => [3,8,21,34,136,260,275,371,376,385,416,420,440,545,591,663,711,746,780,781,843,856,876,957,1025,1037,1146]
  | 252 => [3,8,21,34,136,260,371,376,385,416,420,440,545,591,663,711,746,780,781,843,856,957,1025,1037,1146,1153]
  | 253 => [3,8,21,34,149,186,214,260,267,275,371,382,416,420,440,594,619,670,708,711,719,746,772,780,781,821,843,856,876,986,1081,1157]
  | 254 => [3,8,21,34,149,186,214,260,267,371,382,416,420,440,594,619,670,708,711,719,746,772,780,781,821,843,856,986,1081,1153,1157]
  | 255 => [3,8,21,34,149,186,214,260,275,371,382,416,420,440,594,619,670,708,711,719,746,780,781,843,856,876,986,1081,1146]
  | 256 => [3,8,21,34,149,186,214,260,371,382,416,420,440,594,619,670,708,711,719,746,780,781,843,856,986,1081,1146,1153]
  | 257 => [3,8,21,34,149,186,260,267,275,371,382,416,420,440,594,670,711,719,746,772,780,781,821,843,856,876,986,1072,1157]
  | 258 => [3,8,21,34,149,186,260,267,371,382,416,420,440,594,670,711,719,746,772,780,781,821,843,856,986,1072,1153,1157]
  | 259 => [3,8,21,34,149,186,260,275,371,382,416,420,440,594,670,711,719,746,780,781,843,856,876,986,1072,1146]
  | 260 => [3,8,21,34,149,186,260,371,382,416,420,440,594,670,711,719,746,780,781,843,856,986,1072,1146,1153]
  | 261 => [3,8,21,34,153,260,267,275,371,384,389,416,420,440,535,548,624,711,746,772,780,781,821,843,856,876,943,995,1037,1157]
  | 262 => [3,8,21,34,153,260,267,371,384,389,416,420,440,535,548,624,711,746,772,780,781,821,843,856,943,995,1037,1153,1157]
  | 263 => [3,8,21,34,153,260,275,371,384,389,416,420,440,535,548,624,711,746,780,781,843,856,876,943,995,1037,1146]
  | 264 => [3,8,21,34,153,260,371,384,389,416,420,440,535,548,624,711,746,780,781,843,856,943,995,1037,1146,1153]
  | 285 => [3,8,21,201,260,267,275,371,400,416,420,440,664,746,772,780,781,790,791,821,843,856,876,1051,1122,1157]
  | 286 => [3,8,21,201,260,267,371,400,416,420,440,664,746,772,780,781,790,791,821,843,856,1051,1122,1153,1157]
  | 287 => [3,8,21,201,260,275,371,400,416,420,440,664,746,780,781,790,791,843,856,876,1051,1122,1146]
  | 288 => [3,8,21,201,260,371,400,416,420,440,664,746,780,781,790,791,843,856,1051,1122,1146,1153]
  | 289 => [3,8,21,224,260,267,275,371,416,420,440,738,746,772,780,781,821,823,843,856,876,1087,1157]
  | 290 => [3,8,21,224,260,267,371,416,420,440,738,746,772,780,781,821,823,843,856,1087,1153,1157]
  | 291 => [3,8,21,224,260,275,371,416,420,440,738,746,780,781,823,843,856,876,1087,1146]
  | 292 => [3,8,21,224,260,371,416,420,440,738,746,780,781,823,843,856,1087,1146,1153]
  | 293 => [3,8,21,232,260,267,275,371,412,416,420,440,631,746,764,772,780,781,791,821,843,856,876,1021,1091,1103,1122,1157]
  | 294 => [3,8,21,232,260,267,371,412,416,420,440,631,746,764,772,780,781,791,821,843,856,1021,1091,1103,1122,1153,1157]
  | 295 => [3,8,21,232,260,275,371,412,416,420,440,631,746,764,780,781,791,843,856,876,1021,1091,1103,1122,1146]
  | 296 => [3,8,21,232,260,371,412,416,420,440,631,746,764,780,781,791,843,856,1021,1091,1103,1122,1146,1153]
  | 333 => [3,19,21,44,127,156,170,260,371,372,378,422,425,440,518,527,547,599,618,665,735,751,807,820,843,856,942,1014,1131,1153]
  | 334 => [3,19,21,44,127,156,260,371,372,378,422,425,440,518,527,547,599,618,665,735,751,807,843,856,942,1007,1014,1131,1153]
  | 335 => [3,19,21,44,127,170,260,371,372,378,422,425,440,518,547,618,665,735,751,807,820,843,856,942,993,1131,1153]
  | 336 => [3,19,21,44,127,260,371,372,378,422,425,440,518,547,618,665,735,751,807,843,856,942,993,1007,1131,1153]
  | 337 => [3,19,21,44,133,168,189,260,371,374,422,425,440,552,582,636,662,665,685,735,751,807,843,856,965,1060,1131,1153]
  | 338 => [3,19,21,44,133,168,260,371,374,422,425,440,552,636,665,685,735,751,807,843,856,965,1035,1131,1153]
  | 339 => [3,19,21,44,135,260,371,375,380,422,425,440,509,521,583,665,735,751,807,843,856,929,971,1007,1131,1153]
  | 345 => [3,19,21,178,260,371,393,422,425,440,621,735,751,766,767,807,843,856,1022,1106,1131,1153]
  | 346 => [3,19,21,207,260,371,422,425,440,699,735,751,803,807,843,856,1065,1131,1153]
  | 421 => [3,21,207,251,260,264,371,404,422,425,440,699,729,735,751,788,793,803,843,856,1065,1131,1143,1153]
  | 422 => [3,21,207,260,264,371,404,422,425,440,699,735,751,788,803,843,856,1065,1126,1131,1153]
  | 423 => [3,21,224,256,260,265,267,275,371,409,416,420,440,738,746,768,772,780,801,815,821,823,843,856,876,1087,1154,1157]
  | 424 => [3,21,224,256,260,265,267,371,409,416,420,440,738,746,768,772,780,801,815,821,823,843,856,1087,1153,1154,1157]
  | 425 => [3,21,224,256,260,265,275,371,409,416,420,440,738,746,768,780,801,815,823,843,856,876,1087,1146,1154]
  | 426 => [3,21,224,256,260,265,371,409,416,420,440,738,746,768,780,801,815,823,843,856,1087,1146,1153,1154]
  | 427 => [3,21,224,256,260,267,275,371,409,416,420,440,738,746,772,780,801,821,823,843,856,876,1087,1144,1157]
  | 428 => [3,21,224,256,260,267,371,409,416,420,440,738,746,772,780,801,821,823,843,856,1087,1144,1153,1157]
  | 429 => [3,21,224,256,260,275,371,409,416,420,440,738,746,780,801,823,843,856,876,1087,1144,1146]
  | 430 => [3,21,224,256,260,371,409,416,420,440,738,746,780,801,823,843,856,1087,1144,1146,1153]
  | 431 => [3,21,244,260,270,282,286,287,371,417,419,440,782,784,805,811,831,837,843,846,852,853,856,1117,1173,1181]
  | 432 => [3,21,244,260,270,282,286,371,417,419,440,782,784,805,831,837,843,846,853,856,1117,1165,1173]
  | 433 => [3,21,244,260,270,282,287,371,417,419,440,782,784,811,831,837,843,852,853,856,1117,1164,1181]
  | 434 => [3,21,244,260,270,282,371,417,419,440,782,784,831,837,843,853,856,1117,1164,1165]
  | 450 => [3,21,259,260,275,277,285,371,420,440,780,827,836,843,856,863,870,876,1156,1182]
  | 451 => [3,21,259,260,275,277,295,371,420,439,440,780,827,836,843,856,870,876,1156,1184]
  | 452 => [3,21,259,260,275,277,295,371,420,440,780,827,836,843,855,856,870,876,1156,1183]
  | 453 => [3,21,259,260,275,277,371,420,440,780,827,836,843,856,863,870,876,1156,1161,1184]
  | 494 => [3,21,260,275,276,371,440,442,804,843,856,862,1142]
  | 495 => [3,21,260,275,277,284,285,371,420,429,440,780,827,843,856,863,870,876,879,1156]
  | 496 => [3,21,260,275,277,284,285,371,420,440,780,819,827,843,856,863,870,876,891,1156]
  | 497 => [3,21,260,275,277,284,295,371,420,429,439,440,780,827,843,856,870,876,881,1156]
  | 498 => [3,21,260,275,277,284,295,371,420,429,440,780,827,843,855,856,870,876,883,1156]
  | 499 => [3,21,260,275,277,284,295,371,420,439,440,780,819,827,843,856,870,876,892,1156]
  | 500 => [3,21,260,275,277,284,295,371,420,440,780,819,827,843,855,856,870,876,894,1156]
  | 501 => [3,21,260,275,277,284,371,420,429,440,780,827,843,856,863,870,876,881,1156,1161]
  | 502 => [3,21,260,275,277,284,371,420,440,780,819,827,843,856,863,870,876,892,1156,1161]
  | 503 => [3,21,260,275,277,285,371,420,440,780,827,836,843,856,863,870,876,879,1139,1156]
  | 505 => [3,21,260,275,277,295,371,420,439,440,780,827,836,843,856,870,876,881,1139,1156]
  | 507 => [3,21,260,275,277,295,371,420,440,780,827,836,843,855,856,870,876,883,1139,1156]
  | 509 => [3,21,260,275,277,371,420,440,780,827,836,843,856,863,870,876,881,1139,1156,1161]
  | 511 => [3,21,260,275,277,371,440,442,827,843,856,870,1156]
  | 512 => [3,21,260,276,371,425,440,751,804,843,856,862,1142,1153]
  | 513 => [3,21,260,277,371,420,440,780,827,843,856,870,1153,1156]
  | _ => []
private def src6 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,814,7,807,19,207,699,803,1065]]
private def recs6 : List LowerHistoryRecord := [⟨.left,6,0,(-1),false,209,1174⟩]
private theorem check6 : recs6.all (recordCheck path6 src6 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path6_binding : lowerHistoryPathBinding path6 := by
  apply pathBinding_from_ids path6 src6 [] recs6 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source6 rfl records6 rfl
  · intro r hr _
    simp only [recs6, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise209)
  · intro r hr _
    simp only [recs6, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path6] using WitnessLookup20.witness1174_projection
  · exact check6
  · exact BatchCoverage15.coverage_sound path6 recs6
      records6 SourceValues20.length6 BatchCoverageAll20.coverage6
private def src7 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,277,827,870,1156]]
private def recs7 : List LowerHistoryRecord := [⟨.left,7,0,(-1),false,511,1192⟩]
private theorem check7 : recs7.all (recordCheck path7 src7 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path7_binding : lowerHistoryPathBinding path7 := by
  apply pathBinding_from_ids path7 src7 [] recs7 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source7 rfl records7 rfl
  · intro r hr _
    simp only [recs7, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise511)
  · intro r hr _
    simp only [recs7, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path7] using WitnessLookup20.witness1192_projection
  · exact check7
  · exact BatchCoverage15.coverage_sound path7 recs7
      records7 SourceValues20.length7 BatchCoverageAll20.coverage7
private def src8 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,817,5,1125,408,695,1096,407,675,758,1020,212]]
private def recs8 : List LowerHistoryRecord := [⟨.left,8,0,(-1),false,117,1144⟩]
private theorem check8 : recs8.all (recordCheck path8 src8 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path8_binding : lowerHistoryPathBinding path8 := by
  apply pathBinding_from_ids path8 src8 [] recs8 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source8 rfl records8 rfl
  · intro r hr _
    simp only [recs8, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise117)
  · intro r hr _
    simp only [recs8, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path8] using WitnessLookup20.witness1144_projection
  · exact check8
  · exact BatchCoverage15.coverage_sound path8 recs8
      records8 SourceValues20.length8 BatchCoverageAll20.coverage8
private def src9 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,817,5,1125,411,734,1113,402,693,787,1048,205],[371,843,260,440,3,856,21,275,442,817,5,1125,411,734,243,775,704,1134,402,693,787,1048,205],[371,843,260,440,3,856,21,275,442,817,5,250,868,411,734,1113,402,693,787,1048,205],[371,843,260,440,3,856,21,275,442,817,5,250,868,411,734,243,775,704,1134,402,693,787,1048,205]]
private def recs9 : List LowerHistoryRecord := [⟨.left,9,0,(-1),false,114,1162⟩,⟨.left,9,1,(-1),false,108,1162⟩,⟨.left,9,2,(-1),false,111,1162⟩,⟨.left,9,3,(-1),false,105,1162⟩]
private theorem check9 : recs9.all (recordCheck path9 src9 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path9_binding : lowerHistoryPathBinding path9 := by
  apply pathBinding_from_ids path9 src9 [] recs9 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source9 rfl records9 rfl
  · intro r hr _
    simp only [recs9, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise114)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise108)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise111)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise105)
  · intro r hr _
    simp only [recs9, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [wids, path9] using WitnessLookup20.witness1162_projection
    · simpa only [wids, path9] using WitnessLookup20.witness1162_projection
    · simpa only [wids, path9] using WitnessLookup20.witness1162_projection
    · simpa only [wids, path9] using WitnessLookup20.witness1162_projection
  · exact check9
  · exact BatchCoverage15.coverage_sound path9 recs9
      records9 SourceValues20.length9 BatchCoverageAll20.coverage9
private def src10 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,817,5,256,801,1144,409,738,823,1087,224],[371,843,260,440,3,856,21,275,442,817,5,256,801,265,815,768,1154,409,738,823,1087,224]]
private def recs10 : List LowerHistoryRecord := [⟨.left,10,0,(-1),false,126,1180⟩,⟨.left,10,1,(-1),false,123,1180⟩]
private theorem check10 : recs10.all (recordCheck path10 src10 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path10_binding : lowerHistoryPathBinding path10 := by
  apply pathBinding_from_ids path10 src10 [] recs10 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source10 rfl records10 rfl
  · intro r hr _
    simp only [recs10, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise126)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise123)
  · intro r hr _
    simp only [recs10, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [wids, path10] using WitnessLookup20.witness1180_projection
    · simpa only [wids, path10] using WitnessLookup20.witness1180_projection
  · exact check10
  · exact BatchCoverage15.coverage_sound path10 recs10
      records10 SourceValues20.length10 BatchCoverageAll20.coverage10
end BatchIdSolution0
theorem _root_.solution : lowerHistoryBindingBatch 5 10 := by
  intro i hlo hhi p hp
  interval_cases i
  · have he := Option.some.inj (PathLookup20.path6_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path6_binding
  · have he := Option.some.inj (PathLookup20.path7_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path7_binding
  · have he := Option.some.inj (PathLookup20.path8_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path8_binding
  · have he := Option.some.inj (PathLookup20.path9_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path9_binding
  · have he := Option.some.inj (PathLookup20.path10_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path10_binding
end M7Binding0Sep15
#print axioms solution
