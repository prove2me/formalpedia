-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0140_0145
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T15:40:49.420133+00:00
-- url     : https://prove2.me/submissions/3088a650-cb3a-4f42-9169-9c1f994709f8

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
private theorem norm42 : lowerHistoryNormalization ([2,1],[3]) true false = ⟨true,false,⟨⟨(7/10),0,0,(1/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm43 : lowerHistoryNormalization ([2,1,1],[3]) true true = ⟨true,true,⟨⟨(11/47),0,0,(4/329)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm44 : lowerHistoryNormalization ([2,1,1],[3,1]) false false = ⟨false,false,⟨⟨(43/94),0,0,(37/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm47 : lowerHistoryNormalization ([2,1,1,1],[3,1]) true false = ⟨true,false,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm48 : lowerHistoryNormalization ([2,1,1,1],[3,1]) false false = ⟨false,false,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm49 : lowerHistoryNormalization ([2,1,1,1,3],[3,1]) true true = ⟨true,true,⟨⟨(7377/165722),0,0,(-605/165722)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm50 : lowerHistoryNormalization ([2,1,1,1,3,1],[3,1]) true true = ⟨true,true,⟨⟨(14703/411062),0,0,(-2185/411062)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(3317/8746),0,0,(-1/8746)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm51 : lowerHistoryNormalization ([2,1,1,1,2],[3,1]) true true = ⟨true,true,⟨⟨(163/5134),0,0,(93/25670)⟩,⟨(63/170),0,0,(1/510)⟩,⟨(579/1510),0,0,(-1/1510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm52 : lowerHistoryNormalization ([2,1,1,1,2,1],[3,1]) true true = ⟨true,true,⟨⟨(6229/392530),0,0,(301/392530)⟩,⟨(63/170),0,0,(1/510)⟩,⟨(1759/4618),0,0,(-1/4618)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm53 : lowerHistoryNormalization ([2,1,1,1,1],[3,1]) true false = ⟨true,false,⟨⟨(5937/87770),0,0,(707/87770)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm54 : lowerHistoryNormalization ([2,1,1,1,1,1],[3,1]) true true = ⟨true,true,⟨⟨(205/7906),0,0,(121/39530)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(227/590),0,0,(-1/1770)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm55 : lowerHistoryNormalization ([2,1,1],[3,1]) true false = ⟨true,false,⟨⟨(43/94),0,0,(37/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm56 : lowerHistoryNormalization ([2,1,1,1],[3,1]) true true = ⟨true,true,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey108 : lowerHistoryPull (lowerHistoryH2) ([2,1],[3]) true = ⟨false,true,⟨⟨(14844131850/16611163283),(-22622450/16611163283),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey109 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) true = ⟨false,false,⟨⟨(123317000/92840319),(-6536000/278520957),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey110 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,1],[3]) true = ⟨false,false,⟨⟨(437151/916486),(1064107/2749458),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey111 : lowerHistoryPull (lowerHistoryH23) ([2,1],[3]) true = ⟨false,true,⟨⟨(2754444750/2052479143),(-216932250/2052479143),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey122 : lowerHistoryPull (lowerHistoryH7) ([2,1,1,1],[3,1]) true = ⟨false,false,⟨⟨(1140100/839201),(-323050/839201),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey123 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1],[3,1]) true = ⟨false,true,⟨⟨(387429/2003254),(677093/6009762),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey124 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1],[3,1]) true = ⟨true,false,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey125 : lowerHistoryPull (lowerHistoryH7) ([2,1,1,1],[3,1]) false = ⟨true,false,⟨⟨(46348286/642787275),(4919669/257114910),0,0⟩,⟨(231/611),(1/1833),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey126 : lowerHistoryPull (lowerHistoryH2) ([2,1,1,1,3],[3,1]) true = ⟨false,true,⟨⟨(764894239450/22225157013397),(15834078350/66675471040191),0,0⟩,⟨(33275/87889),(-1/87889),0,0⟩,⟨(30631/80882),(1/242646),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey127 : lowerHistoryPull (lowerHistoryH7) ([2,1,1,1,3,1],[3,1]) true = ⟨false,false,⟨⟨(285443550/5017062413),(-244429700/15051187239),0,0⟩,⟨(3435/9074),(1/27222),0,0⟩,⟨(15965/42157),(-1/42157),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey128 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1,3,1],[3,1]) true = ⟨false,true,⟨⟨(9228439/1147597854),(5376511/1147597854),0,0⟩,⟨(3435/9074),(1/27222),0,0⟩,⟨(15965/42157),(-1/42157),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey129 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1,3,1],[3,1]) true = ⟨true,false,⟨⟨(14703/411062),0,0,(-2185/411062)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(3317/8746),0,0,(-1/8746)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey130 : lowerHistoryPull (lowerHistoryH9) ([2,1,1,1],[3,1]) false = ⟨false,false,⟨⟨(1208703/351923),(-659041/351923),0,0⟩,⟨(7/23),(1/23),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey131 : lowerHistoryPull (lowerHistoryH2) ([2,1,1,1,2],[3,1]) true = ⟨false,true,⟨⟨(1346119055150/22945528938527),(8480504750/22945528938527),0,0⟩,⟨(19756/52033),(-1/52033),0,0⟩,⟨(53579/141046),(1/141046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey132 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,2],[3,1]) true = ⟨false,false,⟨⟨(1878080276500/25150524470163),(39596495000/25150524470163),0,0⟩,⟨(53579/141046),(1/141046),0,0⟩,⟨(2716/7141),(-1/7141),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey133 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,1,1,1,2],[3,1]) true = ⟨false,false,⟨⟨(6319889/259153444),(18166799/777460332),0,0⟩,⟨(1157/3047),(1/9141),0,0⟩,⟨(88962/233893),(-1/233893),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey134 : lowerHistoryPull (lowerHistoryH23) ([2,1,1,1,2],[3,1]) true = ⟨false,true,⟨⟨(258603863250/3079723119187),(-11120246750/3079723119187),0,0⟩,⟨(53579/141046),(1/141046),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey135 : lowerHistoryPull (lowerHistoryH7) ([2,1,1,1,2,1],[3,1]) true = ⟨false,false,⟨⟨(595971350/6179742833),(-169638300/6179742833),0,0⟩,⟨(6167/16246),(1/16246),0,0⟩,⟨(9322/24541),(-1/24541),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey136 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1,2,1],[3,1]) true = ⟨false,true,⟨⟨(5449447/398693086),(9524269/1196079258),0,0⟩,⟨(6167/16246),(1/16246),0,0⟩,⟨(9322/24541),(-1/24541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey137 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1,2,1],[3,1]) true = ⟨true,false,⟨⟨(6229/392530),0,0,(301/392530)⟩,⟨(63/170),0,0,(1/510)⟩,⟨(1759/4618),0,0,(-1/4618)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey138 : lowerHistoryPull (lowerHistoryH2) ([2,1,1,1,1],[3,1]) true = ⟨false,true,⟨⟨(216319037850/1777699342549),(3376499150/5333098027647),0,0⟩,⟨(3247/8507),(-1/25521),0,0⟩,⟨(25537/66838),(1/66838),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey139 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,1],[3,1]) true = ⟨false,false,⟨⟨(94485848500/573572201883),(6917647000/5162149816947),0,0⟩,⟨(25537/66838),(1/66838),0,0⟩,⟨(395/1031),(-1/3093),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey140 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,1,1,1,1],[3,1]) true = ⟨false,false,⟨⟨(1612277/29514484),(1518393/29514484),0,0⟩,⟨(1700/4453),(1/4453),0,0⟩,⟨(38727/101077),(-1/101077),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey141 : lowerHistoryPull (lowerHistoryH23) ([2,1,1,1,1],[3,1]) true = ⟨false,true,⟨⟨(228623250/1262899651),(-355171250/29046691973),0,0⟩,⟨(25537/66838),(1/66838),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey142 : lowerHistoryPull (lowerHistoryH7) ([2,1,1,1,1,1],[3,1]) true = ⟨false,false,⟨⟨(6278550/31709249),(-5335700/95127747),0,0⟩,⟨(3085/8086),(1/8086),0,0⟩,⟨(1485/3887),(-1/11661),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey143 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1,1,1],[3,1]) true = ⟨false,true,⟨⟨(204499/7253142),(119131/7253142),0,0⟩,⟨(3085/8086),(1/8086),0,0⟩,⟨(1485/3887),(-1/11661),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey144 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1,1,1],[3,1]) true = ⟨true,false,⟨⟨(205/7906),0,0,(121/39530)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(227/590),0,0,(-1/1770)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey145 : lowerHistoryPull (lowerHistoryH2) ([2,1,1],[3,1]) true = ⟨false,true,⟨⟨(8603517050/10310778049),(45310050/10310778049),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey146 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) true = ⟨false,false,⟨⟨(124480872500/110611274499),(1112783000/110611274499),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey147 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,1,1],[3,1]) true = ⟨false,false,⟨⟨(1196893/3209954),(6769901/19259724),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(1929/4946),(-1/14838),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey148 : lowerHistoryPull (lowerHistoryH23) ([2,1,1],[3,1]) true = ⟨false,true,⟨⟨(23558673500/19023740021),(-1556463500/19023740021),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pull124 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) true = ⟨true,false,⟨⟨(14844131850/16611163283),(-22622450/16611163283),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey108]
  rfl
private theorem pull141 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH7) ([2,1,1,1],[3,1]) false = ⟨false,true,⟨⟨(46348286/642787275),(4919669/257114910),0,0⟩,⟨(231/611),(1/1833),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey125]
  rfl
private theorem pull149 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,2],[3,1]) true = ⟨true,false,⟨⟨(1346119055150/22945528938527),(8480504750/22945528938527),0,0⟩,⟨(19756/52033),(-1/52033),0,0⟩,⟨(53579/141046),(1/141046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey131]
  rfl
private theorem pull157 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,1],[3,1]) true = ⟨true,false,⟨⟨(216319037850/1777699342549),(3376499150/5333098027647),0,0⟩,⟨(3247/8507),(-1/25521),0,0⟩,⟨(25537/66838),(1/66838),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey138]
  rfl
private theorem pull165 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) true = ⟨true,false,⟨⟨(8603517050/10310778049),(45310050/10310778049),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey145]
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
private theorem branchesG6 :
    (lowerHistoryNecessary ⟨⟨([2,2,2],[3,1,3,1]),(false,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,2],[3,1]) = some [⟨false,false,⟨⟨(21019/31993),(166288/95979),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [⟨false,false,⟨⟨(16971/22607),(33730/22607),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [⟨false,false,⟨⟨(13766/50713),(29019/50713),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [⟨true,false,⟨⟨(-2396241/3388429),(1794784/3388429),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,1,3],[3,1]) = some [⟨false,false,⟨⟨(17414528/312797329),(41514444/312797329),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,1,2],[3,1]) = some [⟨false,false,⟨⟨(405277/4216979),(1100652/4216979),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(188333/700271),(1121999/2100813),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [⟨true,false,⟨⟨(-271911/1001627),(203584/1001627),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩]) := by
  decide +kernel
private theorem branchesG7 :
    (lowerHistoryNecessary ⟨⟨([2,2,1,1,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,1,1,3],[3,1]) = some [⟨false,false,⟨⟨(14928072/698102327),(107382092/2094306981),0,0⟩,⟨(231/611),(1/1833),0,0⟩,⟨(33275/87889),(-1/87889),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1,3,1],[3,1]) = some [⟨false,false,⟨⟨(298695031/17701635601),(223705319/17701635601),0,0⟩,⟨(33275/87889),(-1/87889),0,0⟩,⟨(5866/15493),(1/15493),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,1,1,2],[3,1]) = some [⟨false,false,⟨⟨(94960/2585869),(259781/2585869),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1,2,1],[3,1]) = some [⟨false,false,⟨⟨(134877/6694259),(745220/20082777),0,0⟩,⟨(1157/3047),(1/9141),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(731824/7179887),(1465575/7179887),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(1923725/49263539),(3840076/49263539),0,0⟩,⟨(1700/4453),(1/4453),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [⟨false,false,⟨⟨(34974/50713),(213073/152139),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(188333/700271),(1121999/2100813),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
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
private theorem singleton_removeAll_of_mem {a : CertBound} {l : List CertBound}
    (h : a ∈ l) : [a].removeAll l = [] := by
  simp [List.removeAll, h]
end BindingSourceSupport17

open Freiman
open RootOps19
set_option linter.all false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace BindingOps17_141
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b6 : CertBound) (b21 : CertBound) (b244 : CertBound) (b260 : CertBound) (b282 : CertBound) (b287 : CertBound) (b371 : CertBound) (b419 : CertBound) (b440 : CertBound) (b782 : CertBound) (b784 : CertBound) (b810 : CertBound) (b811 : CertBound) (b837 : CertBound) (b843 : CertBound) (b852 : CertBound) (b853 : CertBound) (b856 : CertBound) (b1117 : CertBound) (b1165 : CertBound) (b1181 : CertBound)
private def path : LowerHistoryPath := ⟨.left,141,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (hb2 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (hb3 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (hb4 : ops.necessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1],[3,1]) = some [b782])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) true false = b282)
    (hn2 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) true = b287)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) true = b852)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1],[3]) true = b811)
    (hn6 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (hn7 : ops.normalization ([2,1,1],[3]) true true = b419)
    (hn8 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (hn9 : ops.normalization ([2,1,1,1],[3,1]) true false = b244)
    (hn10 : ops.pull (lowerHistoryH7) ([2,1,1,1],[3,1]) true = b853)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1],[3,1]) true = b1117)
    (hn12 : ops.pull (lowerHistoryHN) ([2,1,1,1],[3,1]) true = b244)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b244,b782,b853,b1117,b244].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b244,b782,b853,b1117],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b244,b782,b853,b1117]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b244,b782,b853,b1117,b244].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b244,b782,b853,b1117],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b244,b782,b853,b1117]
] : List (List CertBound))[1])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b244,b782,b853,b1117],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b244,b782,b853,b1117]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1]
  rfl
end BindingOps17_141
namespace BindingOps17_142
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b6 : CertBound) (b13 : CertBound) (b21 : CertBound) (b196 : CertBound) (b260 : CertBound) (b282 : CertBound) (b287 : CertBound) (b371 : CertBound) (b397 : CertBound) (b403 : CertBound) (b419 : CertBound) (b440 : CertBound) (b590 : CertBound) (b609 : CertBound) (b691 : CertBound) (b769 : CertBound) (b784 : CertBound) (b810 : CertBound) (b811 : CertBound) (b837 : CertBound) (b843 : CertBound) (b852 : CertBound) (b856 : CertBound) (b969 : CertBound) (b1039 : CertBound) (b1078 : CertBound) (b1165 : CertBound) (b1181 : CertBound)
private def path : LowerHistoryPath := ⟨.left,142,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (hb2 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (hb3 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (hb4 : ops.necessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [b13])
    (hb5 : ops.necessary ⟨⟨([2,2,1,1,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,1,1,3],[3,1]) = some [b609])
    (hb6 : ops.necessary ⟨⟨([2,2,1,1,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1,3,1],[3,1]) = some [b590])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) true false = b282)
    (hn2 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) true = b287)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) true = b852)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1],[3]) true = b811)
    (hn6 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (hn7 : ops.normalization ([2,1,1],[3]) true true = b419)
    (hn8 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (hn9 : ops.normalization ([2,1,1,1],[3,1]) false false = b769)
    (hn10 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,1,1,1],[3,1]) false = b1078)
    (hn11 : ops.normalization ([2,1,1,1,3],[3,1]) true true = b403)
    (hn12 : ops.pull (lowerHistoryH2) ([2,1,1,1,3],[3,1]) true = b1039)
    (hn13 : ops.normalization ([2,1,1,1,3,1],[3,1]) true true = b397)
    (hn14 : ops.pull (lowerHistoryH7) ([2,1,1,1,3,1],[3,1]) true = b691)
    (hn15 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1,3,1],[3,1]) true = b969)
    (hn16 : ops.pull (lowerHistoryHN) ([2,1,1,1,3,1],[3,1]) true = b196)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b1039,b397,b590,b691,b969,b196].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b1039,b397,b590,b691,b969,b196],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b1039,b397,b590,b691,b969,b196]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b1039,b397,b590,b691,b969,b196].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b1039,b397,b590,b691,b969,b196],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b1039,b397,b590,b691,b969,b196]
] : List (List CertBound))[1])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b1039,b397,b590,b691,b969,b196],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b403,b609,b1039,b397,b590,b691,b969,b196]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice4 : lowerHistorySourceChoices ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH7]] := by rfl
  have hdone4 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced4 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice5 : lowerHistorySourceChoices ⟨⟨([2,2,1,1,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hdone5 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced5 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, hchoice4, hdone4, hforced4, hchoice5, hdone5, hforced5, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1]
  rfl
end BindingOps17_142
namespace BindingOps17_143
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b6 : CertBound) (b13 : CertBound) (b21 : CertBound) (b159 : CertBound) (b215 : CertBound) (b220 : CertBound) (b260 : CertBound) (b282 : CertBound) (b287 : CertBound) (b371 : CertBound) (b387 : CertBound) (b396 : CertBound) (b419 : CertBound) (b440 : CertBound) (b602 : CertBound) (b616 : CertBound) (b653 : CertBound) (b706 : CertBound) (b725 : CertBound) (b769 : CertBound) (b784 : CertBound) (b810 : CertBound) (b811 : CertBound) (b837 : CertBound) (b843 : CertBound) (b852 : CertBound) (b856 : CertBound) (b869 : CertBound) (b990 : CertBound) (b1073 : CertBound) (b1078 : CertBound) (b1082 : CertBound) (b1165 : CertBound) (b1181 : CertBound)
private def path : LowerHistoryPath := ⟨.left,143,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,8⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (hb2 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (hb3 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (hb4 : ops.necessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [b13])
    (hb5 : ops.necessary ⟨⟨([2,2,1,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,1,1,2],[3,1]) = some [b653])
    (hb6 : ops.necessary ⟨⟨([2,2,1,1,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1,2,1],[3,1]) = some [b602])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) true false = b282)
    (hn2 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) true = b287)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) true = b852)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1],[3]) true = b811)
    (hn6 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (hn7 : ops.normalization ([2,1,1],[3]) true true = b419)
    (hn8 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (hn9 : ops.normalization ([2,1,1,1],[3,1]) false false = b769)
    (hn10 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,1,1,1],[3,1]) false = b1078)
    (hn11 : ops.pull (lowerHistoryH7) ([2,1,1,1],[3,1]) false = b220)
    (hn12 : ops.pull (lowerHistoryH9) ([2,1,1,1],[3,1]) false = b869)
    (hn13 : ops.normalization ([2,1,1,1,2],[3,1]) true true = b396)
    (hn14 : ops.pull (lowerHistoryH2) ([2,1,1,1,2],[3,1]) true = b1073)
    (hn15 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,2],[3,1]) true = b215)
    (hn16 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,2],[3,1]) true = b706)
    (hn17 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1,1,1,2],[3,1]) true = b616)
    (hn18 : ops.pull (lowerHistoryH23) ([2,1,1,1,2],[3,1]) true = b1082)
    (hn19 : ops.normalization ([2,1,1,1,2,1],[3,1]) true true = b387)
    (hn20 : ops.pull (lowerHistoryH7) ([2,1,1,1,2,1],[3,1]) true = b725)
    (hn21 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1,2,1],[3,1]) true = b990)
    (hn22 : ops.pull (lowerHistoryHN) ([2,1,1,1,2,1],[3,1]) true = b159)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159]
] : List (List CertBound))[1])
    (herase2 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159]
] : List (List CertBound))[2])
    (herase3 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159]
] : List (List CertBound))[3])
    (herase4 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159]
] : List (List CertBound))[4])
    (herase5 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159]
] : List (List CertBound))[5])
    (herase6 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159]
] : List (List CertBound))[6])
    (herase7 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159]
] : List (List CertBound))[7])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b1078,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b1073,b387,b602,b725,b990,b159],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b220,b869,b396,b653,b215,b706,b616,b1082,b387,b602,b725,b990,b159]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice4 : lowerHistorySourceChoices ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hdone4 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced4 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice5 : lowerHistorySourceChoices ⟨⟨([2,2,1,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone5 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced5 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20, hn21, hn22, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, hchoice4, hdone4, hforced4, hchoice5, hdone5, hforced5, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1, herase2, herase3, herase4, herase5, herase6, herase7]
  rfl
end BindingOps17_143
namespace BindingOps17_144
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b6 : CertBound) (b13 : CertBound) (b21 : CertBound) (b179 : CertBound) (b219 : CertBound) (b237 : CertBound) (b260 : CertBound) (b282 : CertBound) (b287 : CertBound) (b371 : CertBound) (b394 : CertBound) (b419 : CertBound) (b440 : CertBound) (b657 : CertBound) (b687 : CertBound) (b728 : CertBound) (b761 : CertBound) (b769 : CertBound) (b771 : CertBound) (b784 : CertBound) (b810 : CertBound) (b811 : CertBound) (b837 : CertBound) (b843 : CertBound) (b852 : CertBound) (b856 : CertBound) (b1026 : CertBound) (b1105 : CertBound) (b1114 : CertBound) (b1165 : CertBound) (b1181 : CertBound)
private def path : LowerHistoryPath := ⟨.left,144,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (hb2 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (hb3 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b6])
    (hb4 : ops.necessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [b13])
    (hb5 : ops.necessary ⟨⟨([2,2,1,1,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1,1],[3,1]) = some [b728])
    (hb6 : ops.necessary ⟨⟨([2,2,1,1,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1,1,1],[3,1]) = some [b657])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) true false = b282)
    (hn2 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) true = b287)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) true = b852)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1],[3]) true = b811)
    (hn6 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (hn7 : ops.normalization ([2,1,1],[3]) true true = b419)
    (hn8 : ops.normalization ([2,1,1],[3,1]) false false = b810)
    (hn9 : ops.normalization ([2,1,1,1],[3,1]) false false = b769)
    (hn10 : ops.normalization ([2,1,1,1,1],[3,1]) true false = b219)
    (hn11 : ops.pull (lowerHistoryH2) ([2,1,1,1,1],[3,1]) true = b1105)
    (hn12 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1,1,1],[3,1]) true = b237)
    (hn13 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1,1,1],[3,1]) true = b761)
    (hn14 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1,1,1,1],[3,1]) true = b687)
    (hn15 : ops.pull (lowerHistoryH23) ([2,1,1,1,1],[3,1]) true = b1114)
    (hn16 : ops.normalization ([2,1,1,1,1,1],[3,1]) true true = b394)
    (hn17 : ops.pull (lowerHistoryH7) ([2,1,1,1,1,1],[3,1]) true = b771)
    (hn18 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1,1,1],[3,1]) true = b1026)
    (hn19 : ops.pull (lowerHistoryHN) ([2,1,1,1,1,1],[3,1]) true = b179)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179]
] : List (List CertBound))[1])
    (herase2 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179]
] : List (List CertBound))[2])
    (herase3 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179]
] : List (List CertBound))[3])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b1105,b394,b657,b771,b1026,b179],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b810,b6,b769,b13,b219,b728,b237,b761,b687,b1114,b394,b657,b771,b1026,b179]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice4 : lowerHistorySourceChoices ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone4 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced4 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice5 : lowerHistorySourceChoices ⟨⟨([2,2,1,1,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone5 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced5 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, hchoice4, hdone4, hforced4, hchoice5, hdone5, hforced5, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1, herase2, herase3]
  rfl
end BindingOps17_144
namespace BindingOps17_145
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b21 : CertBound) (b244 : CertBound) (b260 : CertBound) (b270 : CertBound) (b282 : CertBound) (b286 : CertBound) (b287 : CertBound) (b371 : CertBound) (b417 : CertBound) (b419 : CertBound) (b440 : CertBound) (b782 : CertBound) (b784 : CertBound) (b805 : CertBound) (b811 : CertBound) (b831 : CertBound) (b837 : CertBound) (b843 : CertBound) (b846 : CertBound) (b852 : CertBound) (b853 : CertBound) (b856 : CertBound) (b1117 : CertBound) (b1164 : CertBound) (b1165 : CertBound) (b1173 : CertBound) (b1181 : CertBound)
private def path : LowerHistoryPath := ⟨.left,145,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [b837])
    (hb2 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([2,1,1],[3]) = some [b784])
    (hb3 : ops.necessary ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [b831])
    (hb4 : ops.necessary ⟨⟨([2,2,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1],[3,1]) = some [b782])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) true false = b282)
    (hn2 : ops.pull (lowerHistoryH2) ([2,1],[3]) true = b1165)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) true = b287)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) true = b852)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1],[3]) true = b811)
    (hn6 : ops.pull (lowerHistoryH23) ([2,1],[3]) true = b1181)
    (hn7 : ops.normalization ([2,1,1],[3]) true true = b419)
    (hn8 : ops.normalization ([2,1,1],[3,1]) true false = b270)
    (hn9 : ops.pull (lowerHistoryH2) ([2,1,1],[3,1]) true = b1164)
    (hn10 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) true = b286)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) true = b846)
    (hn12 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1,1],[3,1]) true = b805)
    (hn13 : ops.pull (lowerHistoryH23) ([2,1,1],[3,1]) true = b1173)
    (hn14 : ops.normalization ([2,1,1,1],[3,1]) true true = b417)
    (hn15 : ops.pull (lowerHistoryH7) ([2,1,1,1],[3,1]) true = b853)
    (hn16 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1],[3,1]) true = b1117)
    (hn17 : ops.pull (lowerHistoryHN) ([2,1,1,1],[3,1]) true = b244)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244]
] : List (List CertBound))[1])
    (herase2 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244]
] : List (List CertBound))[2])
    (herase3 : [b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244]
] : List (List CertBound))[3])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b1165,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b856,b21,b282,b837,b287,b852,b811,b1181,b419,b784,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([2,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (true,([],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([2,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1, herase2, herase3]
  rfl
end BindingOps17_145

open Freiman

private abbrev sourceBound3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩

private abbrev sourceBound6 : CertBound := ⟨true,false,⟨⟨(-2396241/3388429),(1794784/3388429),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private abbrev sourceBound13 : CertBound := ⟨true,false,⟨⟨(-271911/1001627),(203584/1001627),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private abbrev sourceBound21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private abbrev sourceBound159 : CertBound := ⟨true,false,⟨⟨(6229/392530),0,0,(301/392530)⟩,⟨(63/170),0,0,(1/510)⟩,⟨(1759/4618),0,0,(-1/4618)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound179 : CertBound := ⟨true,false,⟨⟨(205/7906),0,0,(121/39530)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(227/590),0,0,(-1/1770)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound196 : CertBound := ⟨true,false,⟨⟨(14703/411062),0,0,(-2185/411062)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(3317/8746),0,0,(-1/8746)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound215 : CertBound := ⟨true,false,⟨⟨(1346119055150/22945528938527),(8480504750/22945528938527),0,0⟩,⟨(19756/52033),(-1/52033),0,0⟩,⟨(53579/141046),(1/141046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound219 : CertBound := ⟨true,false,⟨⟨(5937/87770),0,0,(707/87770)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound220 : CertBound := ⟨true,false,⟨⟨(46348286/642787275),(4919669/257114910),0,0⟩,⟨(231/611),(1/1833),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound237 : CertBound := ⟨true,false,⟨⟨(216319037850/1777699342549),(3376499150/5333098027647),0,0⟩,⟨(3247/8507),(-1/25521),0,0⟩,⟨(25537/66838),(1/66838),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound244 : CertBound := ⟨true,false,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound260 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private abbrev sourceBound270 : CertBound := ⟨true,false,⟨⟨(43/94),0,0,(37/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound282 : CertBound := ⟨true,false,⟨⟨(7/10),0,0,(1/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private abbrev sourceBound286 : CertBound := ⟨true,false,⟨⟨(8603517050/10310778049),(45310050/10310778049),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound287 : CertBound := ⟨true,false,⟨⟨(14844131850/16611163283),(-22622450/16611163283),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound371 : CertBound := ⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

private abbrev sourceBound387 : CertBound := ⟨true,true,⟨⟨(6229/392530),0,0,(301/392530)⟩,⟨(63/170),0,0,(1/510)⟩,⟨(1759/4618),0,0,(-1/4618)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound394 : CertBound := ⟨true,true,⟨⟨(205/7906),0,0,(121/39530)⟩,⟨(251/670),0,0,(1/670)⟩,⟨(227/590),0,0,(-1/1770)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound396 : CertBound := ⟨true,true,⟨⟨(163/5134),0,0,(93/25670)⟩,⟨(63/170),0,0,(1/510)⟩,⟨(579/1510),0,0,(-1/1510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound397 : CertBound := ⟨true,true,⟨⟨(14703/411062),0,0,(-2185/411062)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(3317/8746),0,0,(-1/8746)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound403 : CertBound := ⟨true,true,⟨⟨(7377/165722),0,0,(-605/165722)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1341/3526),0,0,(-1/3526)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound417 : CertBound := ⟨true,true,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound419 : CertBound := ⟨true,true,⟨⟨(11/47),0,0,(4/329)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private abbrev sourceBound440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private abbrev sourceBound590 : CertBound := ⟨false,false,⟨⟨(298695031/17701635601),(223705319/17701635601),0,0⟩,⟨(33275/87889),(-1/87889),0,0⟩,⟨(5866/15493),(1/15493),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound602 : CertBound := ⟨false,false,⟨⟨(134877/6694259),(745220/20082777),0,0⟩,⟨(1157/3047),(1/9141),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound609 : CertBound := ⟨false,false,⟨⟨(14928072/698102327),(107382092/2094306981),0,0⟩,⟨(231/611),(1/1833),0,0⟩,⟨(33275/87889),(-1/87889),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound616 : CertBound := ⟨false,false,⟨⟨(6319889/259153444),(18166799/777460332),0,0⟩,⟨(1157/3047),(1/9141),0,0⟩,⟨(88962/233893),(-1/233893),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound653 : CertBound := ⟨false,false,⟨⟨(94960/2585869),(259781/2585869),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound657 : CertBound := ⟨false,false,⟨⟨(1923725/49263539),(3840076/49263539),0,0⟩,⟨(1700/4453),(1/4453),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound687 : CertBound := ⟨false,false,⟨⟨(1612277/29514484),(1518393/29514484),0,0⟩,⟨(1700/4453),(1/4453),0,0⟩,⟨(38727/101077),(-1/101077),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound691 : CertBound := ⟨false,false,⟨⟨(285443550/5017062413),(-244429700/15051187239),0,0⟩,⟨(3435/9074),(1/27222),0,0⟩,⟨(15965/42157),(-1/42157),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound706 : CertBound := ⟨false,false,⟨⟨(1878080276500/25150524470163),(39596495000/25150524470163),0,0⟩,⟨(53579/141046),(1/141046),0,0⟩,⟨(2716/7141),(-1/7141),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private abbrev sourceBound725 : CertBound := ⟨false,false,⟨⟨(595971350/6179742833),(-169638300/6179742833),0,0⟩,⟨(6167/16246),(1/16246),0,0⟩,⟨(9322/24541),(-1/24541),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound728 : CertBound := ⟨false,false,⟨⟨(731824/7179887),(1465575/7179887),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound761 : CertBound := ⟨false,false,⟨⟨(94485848500/573572201883),(6917647000/5162149816947),0,0⟩,⟨(25537/66838),(1/66838),0,0⟩,⟨(395/1031),(-1/3093),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private abbrev sourceBound769 : CertBound := ⟨false,false,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound771 : CertBound := ⟨false,false,⟨⟨(6278550/31709249),(-5335700/95127747),0,0⟩,⟨(3085/8086),(1/8086),0,0⟩,⟨(1485/3887),(-1/11661),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound782 : CertBound := ⟨false,false,⟨⟨(188333/700271),(1121999/2100813),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound784 : CertBound := ⟨false,false,⟨⟨(13766/50713),(29019/50713),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound805 : CertBound := ⟨false,false,⟨⟨(1196893/3209954),(6769901/19259724),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(1929/4946),(-1/14838),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound810 : CertBound := ⟨false,false,⟨⟨(43/94),0,0,(37/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound811 : CertBound := ⟨false,false,⟨⟨(437151/916486),(1064107/2749458),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound831 : CertBound := ⟨false,false,⟨⟨(34974/50713),(213073/152139),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound837 : CertBound := ⟨false,false,⟨⟨(16971/22607),(33730/22607),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound843 : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩

private abbrev sourceBound846 : CertBound := ⟨false,false,⟨⟨(124480872500/110611274499),(1112783000/110611274499),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private abbrev sourceBound852 : CertBound := ⟨false,false,⟨⟨(123317000/92840319),(-6536000/278520957),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(1809/6094),(1/6094),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound853 : CertBound := ⟨false,false,⟨⟨(1140100/839201),(-323050/839201),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound856 : CertBound := ⟨false,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private abbrev sourceBound869 : CertBound := ⟨false,false,⟨⟨(1208703/351923),(-659041/351923),0,0⟩,⟨(7/23),(1/23),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound969 : CertBound := ⟨false,true,⟨⟨(9228439/1147597854),(5376511/1147597854),0,0⟩,⟨(3435/9074),(1/27222),0,0⟩,⟨(15965/42157),(-1/42157),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound990 : CertBound := ⟨false,true,⟨⟨(5449447/398693086),(9524269/1196079258),0,0⟩,⟨(6167/16246),(1/16246),0,0⟩,⟨(9322/24541),(-1/24541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1026 : CertBound := ⟨false,true,⟨⟨(204499/7253142),(119131/7253142),0,0⟩,⟨(3085/8086),(1/8086),0,0⟩,⟨(1485/3887),(-1/11661),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1039 : CertBound := ⟨false,true,⟨⟨(764894239450/22225157013397),(15834078350/66675471040191),0,0⟩,⟨(33275/87889),(-1/87889),0,0⟩,⟨(30631/80882),(1/242646),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1073 : CertBound := ⟨false,true,⟨⟨(1346119055150/22945528938527),(8480504750/22945528938527),0,0⟩,⟨(19756/52033),(-1/52033),0,0⟩,⟨(53579/141046),(1/141046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1078 : CertBound := ⟨false,true,⟨⟨(46348286/642787275),(4919669/257114910),0,0⟩,⟨(231/611),(1/1833),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1082 : CertBound := ⟨false,true,⟨⟨(258603863250/3079723119187),(-11120246750/3079723119187),0,0⟩,⟨(53579/141046),(1/141046),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1105 : CertBound := ⟨false,true,⟨⟨(216319037850/1777699342549),(3376499150/5333098027647),0,0⟩,⟨(3247/8507),(-1/25521),0,0⟩,⟨(25537/66838),(1/66838),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1114 : CertBound := ⟨false,true,⟨⟨(228623250/1262899651),(-355171250/29046691973),0,0⟩,⟨(25537/66838),(1/66838),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1117 : CertBound := ⟨false,true,⟨⟨(387429/2003254),(677093/6009762),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1164 : CertBound := ⟨false,true,⟨⟨(8603517050/10310778049),(45310050/10310778049),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1165 : CertBound := ⟨false,true,⟨⟨(14844131850/16611163283),(-22622450/16611163283),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound1173 : CertBound := ⟨false,true,⟨⟨(23558673500/19023740021),(-1556463500/19023740021),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1181 : CertBound := ⟨false,true,⟨⟨(2754444750/2052479143),(-216932250/2052479143),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

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
open Freiman
namespace SourceMemo17_141
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,141,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound244,sourceBound782,sourceBound853,sourceBound1117],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound244,sourceBound782,sourceBound853,sourceBound1117]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport17.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : ([sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound244,sourceBound782,sourceBound853,sourceBound1117] ++ [sourceBound244]).eraseDups = expected[0] := by
  have hdup : sourceBound244 ∈ expected[0] := by simp [expected]
  change (expected[0] ++ [sourceBound244]).eraseDups = expected[0]
  rw [List.eraseDups_append, erase0,
    BindingSourceSupport17.singleton_removeAll_of_mem hdup,
    List.eraseDups_nil, List.append_nil]
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : ([sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound244,sourceBound782,sourceBound853,sourceBound1117] ++ [sourceBound244]).eraseDups = expected[1] := by
  have hdup : sourceBound244 ∈ expected[1] := by simp [expected]
  change (expected[1] ++ [sourceBound244]).eraseDups = expected[1]
  rw [List.eraseDups_append, erase1,
    BindingSourceSupport17.singleton_removeAll_of_mem hdup,
    List.eraseDups_nil, List.append_nil]
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps17_141.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b6 := sourceBound6) (b21 := sourceBound21) (b244 := sourceBound244) (b260 := sourceBound260) (b282 := sourceBound282) (b287 := sourceBound287) (b371 := sourceBound371) (b419 := sourceBound419) (b440 := sourceBound440) (b782 := sourceBound782) (b784 := sourceBound784) (b810 := sourceBound810) (b811 := sourceBound811) (b837 := sourceBound837) (b843 := sourceBound843) (b852 := sourceBound852) (b853 := sourceBound853) (b856 := sourceBound856) (b1117 := sourceBound1117) (b1165 := sourceBound1165) (b1181 := sourceBound1181)
      BindingSourceSupport17.relaxed2 BindingNumeric17.initial_base (BindingSourceBranches17.branchesG0.1) (BindingSourceBranches17.branchesG6.2.1) (BindingSourceBranches17.branchesG6.2.2.1) (BindingSourceBranches17.branchesG6.2.2.2.1) (BindingSourceBranches17.branchesG6.2.2.2.2.2.2.1) BindingNumeric17.norm0 BindingNumeric17.norm42 BindingNumeric17.pullKey108 BindingNumeric17.pull124 BindingNumeric17.pullKey109 BindingNumeric17.pullKey110 BindingNumeric17.pullKey111 BindingNumeric17.norm43 BindingNumeric17.norm44 BindingNumeric17.norm47 BindingNumeric17.pullKey122 BindingNumeric17.pullKey123 BindingNumeric17.pullKey124 eraseActual0 eraseActual1)
end SourceMemo17_141

open Freiman
open Freiman
namespace SourceMemo17_142
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,142,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound403,sourceBound609,sourceBound1039,sourceBound397,sourceBound590,sourceBound691,sourceBound969,sourceBound196],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound403,sourceBound609,sourceBound1039,sourceBound397,sourceBound590,sourceBound691,sourceBound969,sourceBound196]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport17.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound403,sourceBound609,sourceBound1039,sourceBound397,sourceBound590,sourceBound691,sourceBound969,sourceBound196].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound403,sourceBound609,sourceBound1039,sourceBound397,sourceBound590,sourceBound691,sourceBound969,sourceBound196].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps17_142.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b6 := sourceBound6) (b13 := sourceBound13) (b21 := sourceBound21) (b196 := sourceBound196) (b260 := sourceBound260) (b282 := sourceBound282) (b287 := sourceBound287) (b371 := sourceBound371) (b397 := sourceBound397) (b403 := sourceBound403) (b419 := sourceBound419) (b440 := sourceBound440) (b590 := sourceBound590) (b609 := sourceBound609) (b691 := sourceBound691) (b769 := sourceBound769) (b784 := sourceBound784) (b810 := sourceBound810) (b811 := sourceBound811) (b837 := sourceBound837) (b843 := sourceBound843) (b852 := sourceBound852) (b856 := sourceBound856) (b969 := sourceBound969) (b1039 := sourceBound1039) (b1078 := sourceBound1078) (b1165 := sourceBound1165) (b1181 := sourceBound1181)
      BindingSourceSupport17.relaxed2 BindingNumeric17.initial_base (BindingSourceBranches17.branchesG0.1) (BindingSourceBranches17.branchesG6.2.1) (BindingSourceBranches17.branchesG6.2.2.1) (BindingSourceBranches17.branchesG6.2.2.2.1) (BindingSourceBranches17.branchesG6.2.2.2.2.2.2.2) (BindingSourceBranches17.branchesG7.1) (BindingSourceBranches17.branchesG7.2.1) BindingNumeric17.norm0 BindingNumeric17.norm42 BindingNumeric17.pullKey108 BindingNumeric17.pull124 BindingNumeric17.pullKey109 BindingNumeric17.pullKey110 BindingNumeric17.pullKey111 BindingNumeric17.norm43 BindingNumeric17.norm44 BindingNumeric17.norm48 BindingNumeric17.pull141 BindingNumeric17.norm49 BindingNumeric17.pullKey126 BindingNumeric17.norm50 BindingNumeric17.pullKey127 BindingNumeric17.pullKey128 BindingNumeric17.pullKey129 eraseActual0 eraseActual1)
end SourceMemo17_142

open Freiman
open Freiman
namespace SourceMemo17_143
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,143,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,8⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound396,sourceBound653,sourceBound1073,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound396,sourceBound653,sourceBound215,sourceBound706,sourceBound616,sourceBound1082,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound220,sourceBound869,sourceBound396,sourceBound653,sourceBound1073,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound220,sourceBound869,sourceBound396,sourceBound653,sourceBound215,sourceBound706,sourceBound616,sourceBound1082,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound396,sourceBound653,sourceBound1073,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound396,sourceBound653,sourceBound215,sourceBound706,sourceBound616,sourceBound1082,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound220,sourceBound869,sourceBound396,sourceBound653,sourceBound1073,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound220,sourceBound869,sourceBound396,sourceBound653,sourceBound215,sourceBound706,sourceBound616,sourceBound1082,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport17.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound396,sourceBound653,sourceBound1073,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound396,sourceBound653,sourceBound215,sourceBound706,sourceBound616,sourceBound1082,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem erase2 : expected[2].eraseDups = expected[2] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[2] (by simp [expected])))
private theorem eraseActual2 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound220,sourceBound869,sourceBound396,sourceBound653,sourceBound1073,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159].eraseDups = expected[2] := by
  simpa [expected] using erase2
private theorem erase3 : expected[3].eraseDups = expected[3] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[3] (by simp [expected])))
private theorem eraseActual3 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound220,sourceBound869,sourceBound396,sourceBound653,sourceBound215,sourceBound706,sourceBound616,sourceBound1082,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159].eraseDups = expected[3] := by
  simpa [expected] using erase3
private theorem erase4 : expected[4].eraseDups = expected[4] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[4] (by simp [expected])))
private theorem eraseActual4 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound396,sourceBound653,sourceBound1073,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159].eraseDups = expected[4] := by
  simpa [expected] using erase4
private theorem erase5 : expected[5].eraseDups = expected[5] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[5] (by simp [expected])))
private theorem eraseActual5 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound1078,sourceBound396,sourceBound653,sourceBound215,sourceBound706,sourceBound616,sourceBound1082,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159].eraseDups = expected[5] := by
  simpa [expected] using erase5
private theorem erase6 : expected[6].eraseDups = expected[6] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[6] (by simp [expected])))
private theorem eraseActual6 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound220,sourceBound869,sourceBound396,sourceBound653,sourceBound1073,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159].eraseDups = expected[6] := by
  simpa [expected] using erase6
private theorem erase7 : expected[7].eraseDups = expected[7] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[7] (by simp [expected])))
private theorem eraseActual7 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound220,sourceBound869,sourceBound396,sourceBound653,sourceBound215,sourceBound706,sourceBound616,sourceBound1082,sourceBound387,sourceBound602,sourceBound725,sourceBound990,sourceBound159].eraseDups = expected[7] := by
  simpa [expected] using erase7
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps17_143.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b6 := sourceBound6) (b13 := sourceBound13) (b21 := sourceBound21) (b159 := sourceBound159) (b215 := sourceBound215) (b220 := sourceBound220) (b260 := sourceBound260) (b282 := sourceBound282) (b287 := sourceBound287) (b371 := sourceBound371) (b387 := sourceBound387) (b396 := sourceBound396) (b419 := sourceBound419) (b440 := sourceBound440) (b602 := sourceBound602) (b616 := sourceBound616) (b653 := sourceBound653) (b706 := sourceBound706) (b725 := sourceBound725) (b769 := sourceBound769) (b784 := sourceBound784) (b810 := sourceBound810) (b811 := sourceBound811) (b837 := sourceBound837) (b843 := sourceBound843) (b852 := sourceBound852) (b856 := sourceBound856) (b869 := sourceBound869) (b990 := sourceBound990) (b1073 := sourceBound1073) (b1078 := sourceBound1078) (b1082 := sourceBound1082) (b1165 := sourceBound1165) (b1181 := sourceBound1181)
      BindingSourceSupport17.relaxed2 BindingNumeric17.initial_base (BindingSourceBranches17.branchesG0.1) (BindingSourceBranches17.branchesG6.2.1) (BindingSourceBranches17.branchesG6.2.2.1) (BindingSourceBranches17.branchesG6.2.2.2.1) (BindingSourceBranches17.branchesG6.2.2.2.2.2.2.2) (BindingSourceBranches17.branchesG7.2.2.1) (BindingSourceBranches17.branchesG7.2.2.2.1) BindingNumeric17.norm0 BindingNumeric17.norm42 BindingNumeric17.pullKey108 BindingNumeric17.pull124 BindingNumeric17.pullKey109 BindingNumeric17.pullKey110 BindingNumeric17.pullKey111 BindingNumeric17.norm43 BindingNumeric17.norm44 BindingNumeric17.norm48 BindingNumeric17.pull141 BindingNumeric17.pullKey125 BindingNumeric17.pullKey130 BindingNumeric17.norm51 BindingNumeric17.pullKey131 BindingNumeric17.pull149 BindingNumeric17.pullKey132 BindingNumeric17.pullKey133 BindingNumeric17.pullKey134 BindingNumeric17.norm52 BindingNumeric17.pullKey135 BindingNumeric17.pullKey136 BindingNumeric17.pullKey137 eraseActual0 eraseActual1 eraseActual2 eraseActual3 eraseActual4 eraseActual5 eraseActual6 eraseActual7)
end SourceMemo17_143

open Freiman
open Freiman
namespace SourceMemo17_144
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,144,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound219,sourceBound728,sourceBound1105,sourceBound394,sourceBound657,sourceBound771,sourceBound1026,sourceBound179],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound219,sourceBound728,sourceBound237,sourceBound761,sourceBound687,sourceBound1114,sourceBound394,sourceBound657,sourceBound771,sourceBound1026,sourceBound179],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound219,sourceBound728,sourceBound1105,sourceBound394,sourceBound657,sourceBound771,sourceBound1026,sourceBound179],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound219,sourceBound728,sourceBound237,sourceBound761,sourceBound687,sourceBound1114,sourceBound394,sourceBound657,sourceBound771,sourceBound1026,sourceBound179]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport17.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound219,sourceBound728,sourceBound1105,sourceBound394,sourceBound657,sourceBound771,sourceBound1026,sourceBound179].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound219,sourceBound728,sourceBound237,sourceBound761,sourceBound687,sourceBound1114,sourceBound394,sourceBound657,sourceBound771,sourceBound1026,sourceBound179].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem erase2 : expected[2].eraseDups = expected[2] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[2] (by simp [expected])))
private theorem eraseActual2 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound219,sourceBound728,sourceBound1105,sourceBound394,sourceBound657,sourceBound771,sourceBound1026,sourceBound179].eraseDups = expected[2] := by
  simpa [expected] using erase2
private theorem erase3 : expected[3].eraseDups = expected[3] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[3] (by simp [expected])))
private theorem eraseActual3 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound810,sourceBound6,sourceBound769,sourceBound13,sourceBound219,sourceBound728,sourceBound237,sourceBound761,sourceBound687,sourceBound1114,sourceBound394,sourceBound657,sourceBound771,sourceBound1026,sourceBound179].eraseDups = expected[3] := by
  simpa [expected] using erase3
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps17_144.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b6 := sourceBound6) (b13 := sourceBound13) (b21 := sourceBound21) (b179 := sourceBound179) (b219 := sourceBound219) (b237 := sourceBound237) (b260 := sourceBound260) (b282 := sourceBound282) (b287 := sourceBound287) (b371 := sourceBound371) (b394 := sourceBound394) (b419 := sourceBound419) (b440 := sourceBound440) (b657 := sourceBound657) (b687 := sourceBound687) (b728 := sourceBound728) (b761 := sourceBound761) (b769 := sourceBound769) (b771 := sourceBound771) (b784 := sourceBound784) (b810 := sourceBound810) (b811 := sourceBound811) (b837 := sourceBound837) (b843 := sourceBound843) (b852 := sourceBound852) (b856 := sourceBound856) (b1026 := sourceBound1026) (b1105 := sourceBound1105) (b1114 := sourceBound1114) (b1165 := sourceBound1165) (b1181 := sourceBound1181)
      BindingSourceSupport17.relaxed2 BindingNumeric17.initial_base (BindingSourceBranches17.branchesG0.1) (BindingSourceBranches17.branchesG6.2.1) (BindingSourceBranches17.branchesG6.2.2.1) (BindingSourceBranches17.branchesG6.2.2.2.1) (BindingSourceBranches17.branchesG6.2.2.2.2.2.2.2) (BindingSourceBranches17.branchesG7.2.2.2.2.1) (BindingSourceBranches17.branchesG7.2.2.2.2.2.1) BindingNumeric17.norm0 BindingNumeric17.norm42 BindingNumeric17.pullKey108 BindingNumeric17.pull124 BindingNumeric17.pullKey109 BindingNumeric17.pullKey110 BindingNumeric17.pullKey111 BindingNumeric17.norm43 BindingNumeric17.norm44 BindingNumeric17.norm48 BindingNumeric17.norm53 BindingNumeric17.pullKey138 BindingNumeric17.pull157 BindingNumeric17.pullKey139 BindingNumeric17.pullKey140 BindingNumeric17.pullKey141 BindingNumeric17.norm54 BindingNumeric17.pullKey142 BindingNumeric17.pullKey143 BindingNumeric17.pullKey144 eraseActual0 eraseActual1 eraseActual2 eraseActual3)
end SourceMemo17_144

open Freiman
open Freiman
namespace SourceMemo17_145
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,145,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound270,sourceBound831,sourceBound1164,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound270,sourceBound831,sourceBound286,sourceBound846,sourceBound805,sourceBound1173,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound270,sourceBound831,sourceBound1164,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound270,sourceBound831,sourceBound286,sourceBound846,sourceBound805,sourceBound1173,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport17.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound270,sourceBound831,sourceBound1164,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound1165,sourceBound419,sourceBound784,sourceBound270,sourceBound831,sourceBound286,sourceBound846,sourceBound805,sourceBound1173,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem erase2 : expected[2].eraseDups = expected[2] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[2] (by simp [expected])))
private theorem eraseActual2 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound270,sourceBound831,sourceBound1164,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244].eraseDups = expected[2] := by
  simpa [expected] using erase2
private theorem erase3 : expected[3].eraseDups = expected[3] :=
  BindingSourceSupport17.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport17.fingerprint
      (fingerprint_nodup expected[3] (by simp [expected])))
private theorem eraseActual3 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound282,sourceBound837,sourceBound287,sourceBound852,sourceBound811,sourceBound1181,sourceBound419,sourceBound784,sourceBound270,sourceBound831,sourceBound286,sourceBound846,sourceBound805,sourceBound1173,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244].eraseDups = expected[3] := by
  simpa [expected] using erase3
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps17_145.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b21 := sourceBound21) (b244 := sourceBound244) (b260 := sourceBound260) (b270 := sourceBound270) (b282 := sourceBound282) (b286 := sourceBound286) (b287 := sourceBound287) (b371 := sourceBound371) (b417 := sourceBound417) (b419 := sourceBound419) (b440 := sourceBound440) (b782 := sourceBound782) (b784 := sourceBound784) (b805 := sourceBound805) (b811 := sourceBound811) (b831 := sourceBound831) (b837 := sourceBound837) (b843 := sourceBound843) (b846 := sourceBound846) (b852 := sourceBound852) (b853 := sourceBound853) (b856 := sourceBound856) (b1117 := sourceBound1117) (b1164 := sourceBound1164) (b1165 := sourceBound1165) (b1173 := sourceBound1173) (b1181 := sourceBound1181)
      BindingSourceSupport17.relaxed2 BindingNumeric17.initial_base (BindingSourceBranches17.branchesG0.1) (BindingSourceBranches17.branchesG6.2.1) (BindingSourceBranches17.branchesG6.2.2.1) (BindingSourceBranches17.branchesG7.2.2.2.2.2.2.1) (BindingSourceBranches17.branchesG7.2.2.2.2.2.2.2) BindingNumeric17.norm0 BindingNumeric17.norm42 BindingNumeric17.pullKey108 BindingNumeric17.pull124 BindingNumeric17.pullKey109 BindingNumeric17.pullKey110 BindingNumeric17.pullKey111 BindingNumeric17.norm43 BindingNumeric17.norm55 BindingNumeric17.pullKey145 BindingNumeric17.pull165 BindingNumeric17.pullKey146 BindingNumeric17.pullKey147 BindingNumeric17.pullKey148 BindingNumeric17.norm56 BindingNumeric17.pullKey122 BindingNumeric17.pullKey123 BindingNumeric17.pullKey124 eraseActual0 eraseActual1 eraseActual2 eraseActual3)
end SourceMemo17_145

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
private def path141 : LowerHistoryPath := ⟨.left,141,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
private theorem records141 : lowerHistoryRecordsFor path141 = [⟨.left,141,0,(-1),false,204,1004⟩,⟨.left,141,1,(-1),false,203,148⟩] := by
  change lowerHistoryRecordsFor (⟨.left,141,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 141, lowerHistoryRecordsL_list] <;> rfl
private def path142 : LowerHistoryPath := ⟨.left,142,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩
private theorem records142 : lowerHistoryRecordsFor path142 = [⟨.left,142,0,(-1),false,190,870⟩,⟨.left,142,1,(-1),false,189,118⟩] := by
  change lowerHistoryRecordsFor (⟨.left,142,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 142, lowerHistoryRecordsL_list] <;> rfl
private def path143 : LowerHistoryPath := ⟨.left,143,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,8⟩
private theorem records143 : lowerHistoryRecordsFor path143 = [⟨.left,143,0,(-1),false,178,900⟩,⟨.left,143,1,(-1),false,174,900⟩,⟨.left,143,2,(-1),false,176,900⟩,⟨.left,143,3,(-1),false,172,900⟩,⟨.left,143,4,(-1),false,177,124⟩,⟨.left,143,5,(-1),false,173,124⟩,⟨.left,143,6,(-1),false,175,124⟩,⟨.left,143,7,(-1),false,171,124⟩] := by
  change lowerHistoryRecordsFor (⟨.left,143,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 143, lowerHistoryRecordsL_list] <;> rfl
private def path144 : LowerHistoryPath := ⟨.left,144,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩
private theorem records144 : lowerHistoryRecordsFor path144 = [⟨.left,144,0,(-1),false,182,942⟩,⟨.left,144,1,(-1),false,180,942⟩,⟨.left,144,2,(-1),false,181,130⟩,⟨.left,144,3,(-1),false,179,130⟩] := by
  change lowerHistoryRecordsFor (⟨.left,144,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 144, lowerHistoryRecordsL_list] <;> rfl
private def path145 : LowerHistoryPath := ⟨.left,145,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩
private theorem records145 : lowerHistoryRecordsFor path145 = [⟨.left,145,0,(-1),false,434,1004⟩,⟨.left,145,1,(-1),false,432,65⟩,⟨.left,145,2,(-1),false,433,148⟩,⟨.left,145,3,(-1),false,431,148⟩] := by
  change lowerHistoryRecordsFor (⟨.left,145,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 145, lowerHistoryRecordsL_list] <;> rfl
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
private theorem bound6 : lowerHistoryBound 6 = sourceBound6 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[5]? = some sourceBound6 := Eq.refl (some sourceBound6)
  exact (BoundCompact16.global_to_chunk1 5 (by decide)).trans hlocal
private theorem bound13 : lowerHistoryBound 13 = sourceBound13 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[12]? = some sourceBound13 := Eq.refl (some sourceBound13)
  exact (BoundCompact16.global_to_chunk1 12 (by decide)).trans hlocal
private theorem bound21 : lowerHistoryBound 21 = sourceBound21 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[20]? = some sourceBound21 := Eq.refl (some sourceBound21)
  exact (BoundCompact16.global_to_chunk1 20 (by decide)).trans hlocal
private theorem bound159 : lowerHistoryBound 159 = sourceBound159 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[158]? = some sourceBound159 := Eq.refl (some sourceBound159)
  exact (BoundCompact16.global_to_chunk1 158 (by decide)).trans hlocal
private theorem bound179 : lowerHistoryBound 179 = sourceBound179 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[178]? = some sourceBound179 := Eq.refl (some sourceBound179)
  exact (BoundCompact16.global_to_chunk1 178 (by decide)).trans hlocal
private theorem bound196 : lowerHistoryBound 196 = sourceBound196 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[195]? = some sourceBound196 := Eq.refl (some sourceBound196)
  exact (BoundCompact16.global_to_chunk1 195 (by decide)).trans hlocal
private theorem bound215 : lowerHistoryBound 215 = sourceBound215 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[14]? = some sourceBound215 := Eq.refl (some sourceBound215)
  exact (BoundCompact16.global_to_chunk2 14 (by decide)).trans hlocal
private theorem bound219 : lowerHistoryBound 219 = sourceBound219 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[18]? = some sourceBound219 := Eq.refl (some sourceBound219)
  exact (BoundCompact16.global_to_chunk2 18 (by decide)).trans hlocal
private theorem bound220 : lowerHistoryBound 220 = sourceBound220 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[19]? = some sourceBound220 := Eq.refl (some sourceBound220)
  exact (BoundCompact16.global_to_chunk2 19 (by decide)).trans hlocal
private theorem bound237 : lowerHistoryBound 237 = sourceBound237 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[36]? = some sourceBound237 := Eq.refl (some sourceBound237)
  exact (BoundCompact16.global_to_chunk2 36 (by decide)).trans hlocal
private theorem bound244 : lowerHistoryBound 244 = sourceBound244 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[43]? = some sourceBound244 := Eq.refl (some sourceBound244)
  exact (BoundCompact16.global_to_chunk2 43 (by decide)).trans hlocal
private theorem bound260 : lowerHistoryBound 260 = sourceBound260 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[59]? = some sourceBound260 := Eq.refl (some sourceBound260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hlocal
private theorem bound270 : lowerHistoryBound 270 = sourceBound270 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[69]? = some sourceBound270 := Eq.refl (some sourceBound270)
  exact (BoundCompact16.global_to_chunk2 69 (by decide)).trans hlocal
private theorem bound282 : lowerHistoryBound 282 = sourceBound282 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[81]? = some sourceBound282 := Eq.refl (some sourceBound282)
  exact (BoundCompact16.global_to_chunk2 81 (by decide)).trans hlocal
private theorem bound286 : lowerHistoryBound 286 = sourceBound286 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[85]? = some sourceBound286 := Eq.refl (some sourceBound286)
  exact (BoundCompact16.global_to_chunk2 85 (by decide)).trans hlocal
private theorem bound287 : lowerHistoryBound 287 = sourceBound287 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[86]? = some sourceBound287 := Eq.refl (some sourceBound287)
  exact (BoundCompact16.global_to_chunk2 86 (by decide)).trans hlocal
private theorem bound371 : lowerHistoryBound 371 = sourceBound371 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[170]? = some sourceBound371 := Eq.refl (some sourceBound371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hlocal
private theorem bound387 : lowerHistoryBound 387 = sourceBound387 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[186]? = some sourceBound387 := Eq.refl (some sourceBound387)
  exact (BoundCompact16.global_to_chunk2 186 (by decide)).trans hlocal
private theorem bound394 : lowerHistoryBound 394 = sourceBound394 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[193]? = some sourceBound394 := Eq.refl (some sourceBound394)
  exact (BoundCompact16.global_to_chunk2 193 (by decide)).trans hlocal
private theorem bound396 : lowerHistoryBound 396 = sourceBound396 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[195]? = some sourceBound396 := Eq.refl (some sourceBound396)
  exact (BoundCompact16.global_to_chunk2 195 (by decide)).trans hlocal
private theorem bound397 : lowerHistoryBound 397 = sourceBound397 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[196]? = some sourceBound397 := Eq.refl (some sourceBound397)
  exact (BoundCompact16.global_to_chunk2 196 (by decide)).trans hlocal
private theorem bound403 : lowerHistoryBound 403 = sourceBound403 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[2]? = some sourceBound403 := Eq.refl (some sourceBound403)
  exact (BoundCompact16.global_to_chunk3 2 (by decide)).trans hlocal
private theorem bound417 : lowerHistoryBound 417 = sourceBound417 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[16]? = some sourceBound417 := Eq.refl (some sourceBound417)
  exact (BoundCompact16.global_to_chunk3 16 (by decide)).trans hlocal
private theorem bound419 : lowerHistoryBound 419 = sourceBound419 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[18]? = some sourceBound419 := Eq.refl (some sourceBound419)
  exact (BoundCompact16.global_to_chunk3 18 (by decide)).trans hlocal
private theorem bound440 : lowerHistoryBound 440 = sourceBound440 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[39]? = some sourceBound440 := Eq.refl (some sourceBound440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hlocal
private theorem bound590 : lowerHistoryBound 590 = sourceBound590 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[189]? = some sourceBound590 := Eq.refl (some sourceBound590)
  exact (BoundCompact16.global_to_chunk3 189 (by decide)).trans hlocal
private theorem bound602 : lowerHistoryBound 602 = sourceBound602 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[1]? = some sourceBound602 := Eq.refl (some sourceBound602)
  exact (BoundCompact16.global_to_chunk4 1 (by decide)).trans hlocal
private theorem bound609 : lowerHistoryBound 609 = sourceBound609 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[8]? = some sourceBound609 := Eq.refl (some sourceBound609)
  exact (BoundCompact16.global_to_chunk4 8 (by decide)).trans hlocal
private theorem bound616 : lowerHistoryBound 616 = sourceBound616 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[15]? = some sourceBound616 := Eq.refl (some sourceBound616)
  exact (BoundCompact16.global_to_chunk4 15 (by decide)).trans hlocal
private theorem bound653 : lowerHistoryBound 653 = sourceBound653 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[52]? = some sourceBound653 := Eq.refl (some sourceBound653)
  exact (BoundCompact16.global_to_chunk4 52 (by decide)).trans hlocal
private theorem bound657 : lowerHistoryBound 657 = sourceBound657 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[56]? = some sourceBound657 := Eq.refl (some sourceBound657)
  exact (BoundCompact16.global_to_chunk4 56 (by decide)).trans hlocal
private theorem bound687 : lowerHistoryBound 687 = sourceBound687 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[86]? = some sourceBound687 := Eq.refl (some sourceBound687)
  exact (BoundCompact16.global_to_chunk4 86 (by decide)).trans hlocal
private theorem bound691 : lowerHistoryBound 691 = sourceBound691 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[90]? = some sourceBound691 := Eq.refl (some sourceBound691)
  exact (BoundCompact16.global_to_chunk4 90 (by decide)).trans hlocal
private theorem bound706 : lowerHistoryBound 706 = sourceBound706 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[105]? = some sourceBound706 := Eq.refl (some sourceBound706)
  exact (BoundCompact16.global_to_chunk4 105 (by decide)).trans hlocal
private theorem bound725 : lowerHistoryBound 725 = sourceBound725 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[124]? = some sourceBound725 := Eq.refl (some sourceBound725)
  exact (BoundCompact16.global_to_chunk4 124 (by decide)).trans hlocal
private theorem bound728 : lowerHistoryBound 728 = sourceBound728 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[127]? = some sourceBound728 := Eq.refl (some sourceBound728)
  exact (BoundCompact16.global_to_chunk4 127 (by decide)).trans hlocal
private theorem bound761 : lowerHistoryBound 761 = sourceBound761 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[160]? = some sourceBound761 := Eq.refl (some sourceBound761)
  exact (BoundCompact16.global_to_chunk4 160 (by decide)).trans hlocal
private theorem bound769 : lowerHistoryBound 769 = sourceBound769 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[168]? = some sourceBound769 := Eq.refl (some sourceBound769)
  exact (BoundCompact16.global_to_chunk4 168 (by decide)).trans hlocal
private theorem bound771 : lowerHistoryBound 771 = sourceBound771 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[170]? = some sourceBound771 := Eq.refl (some sourceBound771)
  exact (BoundCompact16.global_to_chunk4 170 (by decide)).trans hlocal
private theorem bound782 : lowerHistoryBound 782 = sourceBound782 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[181]? = some sourceBound782 := Eq.refl (some sourceBound782)
  exact (BoundCompact16.global_to_chunk4 181 (by decide)).trans hlocal
private theorem bound784 : lowerHistoryBound 784 = sourceBound784 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[183]? = some sourceBound784 := Eq.refl (some sourceBound784)
  exact (BoundCompact16.global_to_chunk4 183 (by decide)).trans hlocal
private theorem bound805 : lowerHistoryBound 805 = sourceBound805 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[4]? = some sourceBound805 := Eq.refl (some sourceBound805)
  exact (BoundCompact16.global_to_chunk5 4 (by decide)).trans hlocal
private theorem bound810 : lowerHistoryBound 810 = sourceBound810 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[9]? = some sourceBound810 := Eq.refl (some sourceBound810)
  exact (BoundCompact16.global_to_chunk5 9 (by decide)).trans hlocal
private theorem bound811 : lowerHistoryBound 811 = sourceBound811 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[10]? = some sourceBound811 := Eq.refl (some sourceBound811)
  exact (BoundCompact16.global_to_chunk5 10 (by decide)).trans hlocal
private theorem bound831 : lowerHistoryBound 831 = sourceBound831 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[30]? = some sourceBound831 := Eq.refl (some sourceBound831)
  exact (BoundCompact16.global_to_chunk5 30 (by decide)).trans hlocal
private theorem bound837 : lowerHistoryBound 837 = sourceBound837 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[36]? = some sourceBound837 := Eq.refl (some sourceBound837)
  exact (BoundCompact16.global_to_chunk5 36 (by decide)).trans hlocal
private theorem bound843 : lowerHistoryBound 843 = sourceBound843 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[42]? = some sourceBound843 := Eq.refl (some sourceBound843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hlocal
private theorem bound846 : lowerHistoryBound 846 = sourceBound846 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[45]? = some sourceBound846 := Eq.refl (some sourceBound846)
  exact (BoundCompact16.global_to_chunk5 45 (by decide)).trans hlocal
private theorem bound852 : lowerHistoryBound 852 = sourceBound852 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[51]? = some sourceBound852 := Eq.refl (some sourceBound852)
  exact (BoundCompact16.global_to_chunk5 51 (by decide)).trans hlocal
private theorem bound853 : lowerHistoryBound 853 = sourceBound853 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[52]? = some sourceBound853 := Eq.refl (some sourceBound853)
  exact (BoundCompact16.global_to_chunk5 52 (by decide)).trans hlocal
private theorem bound856 : lowerHistoryBound 856 = sourceBound856 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[55]? = some sourceBound856 := Eq.refl (some sourceBound856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hlocal
private theorem bound869 : lowerHistoryBound 869 = sourceBound869 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[68]? = some sourceBound869 := Eq.refl (some sourceBound869)
  exact (BoundCompact16.global_to_chunk5 68 (by decide)).trans hlocal
private theorem bound969 : lowerHistoryBound 969 = sourceBound969 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[168]? = some sourceBound969 := Eq.refl (some sourceBound969)
  exact (BoundCompact16.global_to_chunk5 168 (by decide)).trans hlocal
private theorem bound990 : lowerHistoryBound 990 = sourceBound990 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[189]? = some sourceBound990 := Eq.refl (some sourceBound990)
  exact (BoundCompact16.global_to_chunk5 189 (by decide)).trans hlocal
private theorem bound1026 : lowerHistoryBound 1026 = sourceBound1026 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[25]? = some sourceBound1026 := Eq.refl (some sourceBound1026)
  exact (BoundCompact16.global_to_chunk6 25).trans hlocal
private theorem bound1039 : lowerHistoryBound 1039 = sourceBound1039 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[38]? = some sourceBound1039 := Eq.refl (some sourceBound1039)
  exact (BoundCompact16.global_to_chunk6 38).trans hlocal
private theorem bound1073 : lowerHistoryBound 1073 = sourceBound1073 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[72]? = some sourceBound1073 := Eq.refl (some sourceBound1073)
  exact (BoundCompact16.global_to_chunk6 72).trans hlocal
private theorem bound1078 : lowerHistoryBound 1078 = sourceBound1078 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[77]? = some sourceBound1078 := Eq.refl (some sourceBound1078)
  exact (BoundCompact16.global_to_chunk6 77).trans hlocal
private theorem bound1082 : lowerHistoryBound 1082 = sourceBound1082 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[81]? = some sourceBound1082 := Eq.refl (some sourceBound1082)
  exact (BoundCompact16.global_to_chunk6 81).trans hlocal
private theorem bound1105 : lowerHistoryBound 1105 = sourceBound1105 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[104]? = some sourceBound1105 := Eq.refl (some sourceBound1105)
  exact (BoundCompact16.global_to_chunk6 104).trans hlocal
private theorem bound1114 : lowerHistoryBound 1114 = sourceBound1114 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[113]? = some sourceBound1114 := Eq.refl (some sourceBound1114)
  exact (BoundCompact16.global_to_chunk6 113).trans hlocal
private theorem bound1117 : lowerHistoryBound 1117 = sourceBound1117 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[116]? = some sourceBound1117 := Eq.refl (some sourceBound1117)
  exact (BoundCompact16.global_to_chunk6 116).trans hlocal
private theorem bound1164 : lowerHistoryBound 1164 = sourceBound1164 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[163]? = some sourceBound1164 := Eq.refl (some sourceBound1164)
  exact (BoundCompact16.global_to_chunk6 163).trans hlocal
private theorem bound1165 : lowerHistoryBound 1165 = sourceBound1165 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[164]? = some sourceBound1165 := Eq.refl (some sourceBound1165)
  exact (BoundCompact16.global_to_chunk6 164).trans hlocal
private theorem bound1173 : lowerHistoryBound 1173 = sourceBound1173 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[172]? = some sourceBound1173 := Eq.refl (some sourceBound1173)
  exact (BoundCompact16.global_to_chunk6 172).trans hlocal
private theorem bound1181 : lowerHistoryBound 1181 = sourceBound1181 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[180]? = some sourceBound1181 := Eq.refl (some sourceBound1181)
  exact (BoundCompact16.global_to_chunk6 180).trans hlocal
end BatchLookup17

open Freiman
namespace SourceValues17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem source141 : lowerHistorySourcePremises BatchLookup17.path141 =
    ([[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,244,782,853,1117],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,244,782,853,1117]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound244 (congrArg₂ List.cons BatchLookup17.bound782 (congrArg₂ List.cons BatchLookup17.bound853 (congrArg₂ List.cons BatchLookup17.bound1117 (rfl : ([] : List CertBound) = []))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound244 (congrArg₂ List.cons BatchLookup17.bound782 (congrArg₂ List.cons BatchLookup17.bound853 (congrArg₂ List.cons BatchLookup17.bound1117 (rfl : ([] : List CertBound) = [])))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))
  exact SourceMemo17_141.source.trans hb.symm
private theorem length141 : BatchLookup17.path141.alternatives =
    (lowerHistorySourcePremises BatchLookup17.path141).length := by
  exact (congrArg List.length source141).symm
private theorem source142 : lowerHistorySourcePremises BatchLookup17.path142 =
    ([[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,1078,403,609,1039,397,590,691,969,196],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,1078,403,609,1039,397,590,691,969,196]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound1078 (congrArg₂ List.cons BatchLookup17.bound403 (congrArg₂ List.cons BatchLookup17.bound609 (congrArg₂ List.cons BatchLookup17.bound1039 (congrArg₂ List.cons BatchLookup17.bound397 (congrArg₂ List.cons BatchLookup17.bound590 (congrArg₂ List.cons BatchLookup17.bound691 (congrArg₂ List.cons BatchLookup17.bound969 (congrArg₂ List.cons BatchLookup17.bound196 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound1078 (congrArg₂ List.cons BatchLookup17.bound403 (congrArg₂ List.cons BatchLookup17.bound609 (congrArg₂ List.cons BatchLookup17.bound1039 (congrArg₂ List.cons BatchLookup17.bound397 (congrArg₂ List.cons BatchLookup17.bound590 (congrArg₂ List.cons BatchLookup17.bound691 (congrArg₂ List.cons BatchLookup17.bound969 (congrArg₂ List.cons BatchLookup17.bound196 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))
  exact SourceMemo17_142.source.trans hb.symm
private theorem length142 : BatchLookup17.path142.alternatives =
    (lowerHistorySourcePremises BatchLookup17.path142).length := by
  exact (congrArg List.length source142).symm
private theorem source143 : lowerHistorySourcePremises BatchLookup17.path143 =
    ([[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,1078,396,653,1073,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,1078,396,653,215,706,616,1082,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,220,869,396,653,1073,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,220,869,396,653,215,706,616,1082,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,1078,396,653,1073,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,1078,396,653,215,706,616,1082,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,220,869,396,653,1073,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,220,869,396,653,215,706,616,1082,387,602,725,990,159]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound1078 (congrArg₂ List.cons BatchLookup17.bound396 (congrArg₂ List.cons BatchLookup17.bound653 (congrArg₂ List.cons BatchLookup17.bound1073 (congrArg₂ List.cons BatchLookup17.bound387 (congrArg₂ List.cons BatchLookup17.bound602 (congrArg₂ List.cons BatchLookup17.bound725 (congrArg₂ List.cons BatchLookup17.bound990 (congrArg₂ List.cons BatchLookup17.bound159 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound1078 (congrArg₂ List.cons BatchLookup17.bound396 (congrArg₂ List.cons BatchLookup17.bound653 (congrArg₂ List.cons BatchLookup17.bound215 (congrArg₂ List.cons BatchLookup17.bound706 (congrArg₂ List.cons BatchLookup17.bound616 (congrArg₂ List.cons BatchLookup17.bound1082 (congrArg₂ List.cons BatchLookup17.bound387 (congrArg₂ List.cons BatchLookup17.bound602 (congrArg₂ List.cons BatchLookup17.bound725 (congrArg₂ List.cons BatchLookup17.bound990 (congrArg₂ List.cons BatchLookup17.bound159 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound220 (congrArg₂ List.cons BatchLookup17.bound869 (congrArg₂ List.cons BatchLookup17.bound396 (congrArg₂ List.cons BatchLookup17.bound653 (congrArg₂ List.cons BatchLookup17.bound1073 (congrArg₂ List.cons BatchLookup17.bound387 (congrArg₂ List.cons BatchLookup17.bound602 (congrArg₂ List.cons BatchLookup17.bound725 (congrArg₂ List.cons BatchLookup17.bound990 (congrArg₂ List.cons BatchLookup17.bound159 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound220 (congrArg₂ List.cons BatchLookup17.bound869 (congrArg₂ List.cons BatchLookup17.bound396 (congrArg₂ List.cons BatchLookup17.bound653 (congrArg₂ List.cons BatchLookup17.bound215 (congrArg₂ List.cons BatchLookup17.bound706 (congrArg₂ List.cons BatchLookup17.bound616 (congrArg₂ List.cons BatchLookup17.bound1082 (congrArg₂ List.cons BatchLookup17.bound387 (congrArg₂ List.cons BatchLookup17.bound602 (congrArg₂ List.cons BatchLookup17.bound725 (congrArg₂ List.cons BatchLookup17.bound990 (congrArg₂ List.cons BatchLookup17.bound159 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound1078 (congrArg₂ List.cons BatchLookup17.bound396 (congrArg₂ List.cons BatchLookup17.bound653 (congrArg₂ List.cons BatchLookup17.bound1073 (congrArg₂ List.cons BatchLookup17.bound387 (congrArg₂ List.cons BatchLookup17.bound602 (congrArg₂ List.cons BatchLookup17.bound725 (congrArg₂ List.cons BatchLookup17.bound990 (congrArg₂ List.cons BatchLookup17.bound159 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound1078 (congrArg₂ List.cons BatchLookup17.bound396 (congrArg₂ List.cons BatchLookup17.bound653 (congrArg₂ List.cons BatchLookup17.bound215 (congrArg₂ List.cons BatchLookup17.bound706 (congrArg₂ List.cons BatchLookup17.bound616 (congrArg₂ List.cons BatchLookup17.bound1082 (congrArg₂ List.cons BatchLookup17.bound387 (congrArg₂ List.cons BatchLookup17.bound602 (congrArg₂ List.cons BatchLookup17.bound725 (congrArg₂ List.cons BatchLookup17.bound990 (congrArg₂ List.cons BatchLookup17.bound159 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound220 (congrArg₂ List.cons BatchLookup17.bound869 (congrArg₂ List.cons BatchLookup17.bound396 (congrArg₂ List.cons BatchLookup17.bound653 (congrArg₂ List.cons BatchLookup17.bound1073 (congrArg₂ List.cons BatchLookup17.bound387 (congrArg₂ List.cons BatchLookup17.bound602 (congrArg₂ List.cons BatchLookup17.bound725 (congrArg₂ List.cons BatchLookup17.bound990 (congrArg₂ List.cons BatchLookup17.bound159 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound220 (congrArg₂ List.cons BatchLookup17.bound869 (congrArg₂ List.cons BatchLookup17.bound396 (congrArg₂ List.cons BatchLookup17.bound653 (congrArg₂ List.cons BatchLookup17.bound215 (congrArg₂ List.cons BatchLookup17.bound706 (congrArg₂ List.cons BatchLookup17.bound616 (congrArg₂ List.cons BatchLookup17.bound1082 (congrArg₂ List.cons BatchLookup17.bound387 (congrArg₂ List.cons BatchLookup17.bound602 (congrArg₂ List.cons BatchLookup17.bound725 (congrArg₂ List.cons BatchLookup17.bound990 (congrArg₂ List.cons BatchLookup17.bound159 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))))))))
  exact SourceMemo17_143.source.trans hb.symm
private theorem length143 : BatchLookup17.path143.alternatives =
    (lowerHistorySourcePremises BatchLookup17.path143).length := by
  exact (congrArg List.length source143).symm
private theorem source144 : lowerHistorySourcePremises BatchLookup17.path144 =
    ([[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,219,728,1105,394,657,771,1026,179],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,219,728,237,761,687,1114,394,657,771,1026,179],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,219,728,1105,394,657,771,1026,179],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,219,728,237,761,687,1114,394,657,771,1026,179]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound219 (congrArg₂ List.cons BatchLookup17.bound728 (congrArg₂ List.cons BatchLookup17.bound1105 (congrArg₂ List.cons BatchLookup17.bound394 (congrArg₂ List.cons BatchLookup17.bound657 (congrArg₂ List.cons BatchLookup17.bound771 (congrArg₂ List.cons BatchLookup17.bound1026 (congrArg₂ List.cons BatchLookup17.bound179 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound219 (congrArg₂ List.cons BatchLookup17.bound728 (congrArg₂ List.cons BatchLookup17.bound237 (congrArg₂ List.cons BatchLookup17.bound761 (congrArg₂ List.cons BatchLookup17.bound687 (congrArg₂ List.cons BatchLookup17.bound1114 (congrArg₂ List.cons BatchLookup17.bound394 (congrArg₂ List.cons BatchLookup17.bound657 (congrArg₂ List.cons BatchLookup17.bound771 (congrArg₂ List.cons BatchLookup17.bound1026 (congrArg₂ List.cons BatchLookup17.bound179 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound219 (congrArg₂ List.cons BatchLookup17.bound728 (congrArg₂ List.cons BatchLookup17.bound1105 (congrArg₂ List.cons BatchLookup17.bound394 (congrArg₂ List.cons BatchLookup17.bound657 (congrArg₂ List.cons BatchLookup17.bound771 (congrArg₂ List.cons BatchLookup17.bound1026 (congrArg₂ List.cons BatchLookup17.bound179 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound810 (congrArg₂ List.cons BatchLookup17.bound6 (congrArg₂ List.cons BatchLookup17.bound769 (congrArg₂ List.cons BatchLookup17.bound13 (congrArg₂ List.cons BatchLookup17.bound219 (congrArg₂ List.cons BatchLookup17.bound728 (congrArg₂ List.cons BatchLookup17.bound237 (congrArg₂ List.cons BatchLookup17.bound761 (congrArg₂ List.cons BatchLookup17.bound687 (congrArg₂ List.cons BatchLookup17.bound1114 (congrArg₂ List.cons BatchLookup17.bound394 (congrArg₂ List.cons BatchLookup17.bound657 (congrArg₂ List.cons BatchLookup17.bound771 (congrArg₂ List.cons BatchLookup17.bound1026 (congrArg₂ List.cons BatchLookup17.bound179 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))))
  exact SourceMemo17_144.source.trans hb.symm
private theorem length144 : BatchLookup17.path144.alternatives =
    (lowerHistorySourcePremises BatchLookup17.path144).length := by
  exact (congrArg List.length source144).symm
private theorem source145 : lowerHistorySourcePremises BatchLookup17.path145 =
    ([[371,843,260,440,3,856,21,282,837,1165,419,784,270,831,1164,417,782,853,1117,244],[371,843,260,440,3,856,21,282,837,1165,419,784,270,831,286,846,805,1173,417,782,853,1117,244],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,270,831,1164,417,782,853,1117,244],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,270,831,286,846,805,1173,417,782,853,1117,244]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound270 (congrArg₂ List.cons BatchLookup17.bound831 (congrArg₂ List.cons BatchLookup17.bound1164 (congrArg₂ List.cons BatchLookup17.bound417 (congrArg₂ List.cons BatchLookup17.bound782 (congrArg₂ List.cons BatchLookup17.bound853 (congrArg₂ List.cons BatchLookup17.bound1117 (congrArg₂ List.cons BatchLookup17.bound244 (rfl : ([] : List CertBound) = []))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound1165 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound270 (congrArg₂ List.cons BatchLookup17.bound831 (congrArg₂ List.cons BatchLookup17.bound286 (congrArg₂ List.cons BatchLookup17.bound846 (congrArg₂ List.cons BatchLookup17.bound805 (congrArg₂ List.cons BatchLookup17.bound1173 (congrArg₂ List.cons BatchLookup17.bound417 (congrArg₂ List.cons BatchLookup17.bound782 (congrArg₂ List.cons BatchLookup17.bound853 (congrArg₂ List.cons BatchLookup17.bound1117 (congrArg₂ List.cons BatchLookup17.bound244 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound270 (congrArg₂ List.cons BatchLookup17.bound831 (congrArg₂ List.cons BatchLookup17.bound1164 (congrArg₂ List.cons BatchLookup17.bound417 (congrArg₂ List.cons BatchLookup17.bound782 (congrArg₂ List.cons BatchLookup17.bound853 (congrArg₂ List.cons BatchLookup17.bound1117 (congrArg₂ List.cons BatchLookup17.bound244 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup17.bound371 (congrArg₂ List.cons BatchLookup17.bound843 (congrArg₂ List.cons BatchLookup17.bound260 (congrArg₂ List.cons BatchLookup17.bound440 (congrArg₂ List.cons BatchLookup17.bound3 (congrArg₂ List.cons BatchLookup17.bound856 (congrArg₂ List.cons BatchLookup17.bound21 (congrArg₂ List.cons BatchLookup17.bound282 (congrArg₂ List.cons BatchLookup17.bound837 (congrArg₂ List.cons BatchLookup17.bound287 (congrArg₂ List.cons BatchLookup17.bound852 (congrArg₂ List.cons BatchLookup17.bound811 (congrArg₂ List.cons BatchLookup17.bound1181 (congrArg₂ List.cons BatchLookup17.bound419 (congrArg₂ List.cons BatchLookup17.bound784 (congrArg₂ List.cons BatchLookup17.bound270 (congrArg₂ List.cons BatchLookup17.bound831 (congrArg₂ List.cons BatchLookup17.bound286 (congrArg₂ List.cons BatchLookup17.bound846 (congrArg₂ List.cons BatchLookup17.bound805 (congrArg₂ List.cons BatchLookup17.bound1173 (congrArg₂ List.cons BatchLookup17.bound417 (congrArg₂ List.cons BatchLookup17.bound782 (congrArg₂ List.cons BatchLookup17.bound853 (congrArg₂ List.cons BatchLookup17.bound1117 (congrArg₂ List.cons BatchLookup17.bound244 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))))
  exact SourceMemo17_145.source.trans hb.symm
private theorem length145 : BatchLookup17.path145.alternatives =
    (lowerHistorySourcePremises BatchLookup17.path145).length := by
  exact (congrArg List.length source145).symm
end SourceValues17


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
namespace BatchLookup17
set_option maxRecDepth 30000
private theorem size01 : lowerHistoryPremises01.size = 200 := by rfl
private theorem size02 : lowerHistoryPremises02.size = 200 := by rfl
private theorem size03 : lowerHistoryPremises03.size = 200 := by rfl
private theorem size04 : lowerHistoryPremises04.size = 200 := by rfl
private theorem size05 : lowerHistoryPremises05.size = 200 := by rfl
private theorem premise171 : lowerHistoryPremises[170]? = some ([3, 6, 13, 21, 159, 215, 220, 260, 282, 287, 371, 387, 396, 419, 440, 602, 616, 653, 706, 725, 769, 784, 810, 811, 837, 843, 852, 856, 869, 990, 1082, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 170 = 0+170 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 170 (by decide)]
  rfl
private theorem premise172 : lowerHistoryPremises[171]? = some ([3, 6, 13, 21, 159, 215, 220, 260, 282, 371, 387, 396, 419, 440, 602, 616, 653, 706, 725, 769, 784, 810, 837, 843, 856, 869, 990, 1082, 1165] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 171 = 0+171 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 171 (by decide)]
  rfl
private theorem premise173 : lowerHistoryPremises[172]? = some ([3, 6, 13, 21, 159, 215, 260, 282, 287, 371, 387, 396, 419, 440, 602, 616, 653, 706, 725, 769, 784, 810, 811, 837, 843, 852, 856, 990, 1078, 1082, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 172 = 0+172 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 172 (by decide)]
  rfl
private theorem premise174 : lowerHistoryPremises[173]? = some ([3, 6, 13, 21, 159, 215, 260, 282, 371, 387, 396, 419, 440, 602, 616, 653, 706, 725, 769, 784, 810, 837, 843, 856, 990, 1078, 1082, 1165] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 173 = 0+173 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 173 (by decide)]
  rfl
private theorem premise175 : lowerHistoryPremises[174]? = some ([3, 6, 13, 21, 159, 220, 260, 282, 287, 371, 387, 396, 419, 440, 602, 653, 725, 769, 784, 810, 811, 837, 843, 852, 856, 869, 990, 1073, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 174 = 0+174 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 174 (by decide)]
  rfl
private theorem premise176 : lowerHistoryPremises[175]? = some ([3, 6, 13, 21, 159, 220, 260, 282, 371, 387, 396, 419, 440, 602, 653, 725, 769, 784, 810, 837, 843, 856, 869, 990, 1073, 1165] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 175 = 0+175 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 175 (by decide)]
  rfl
private theorem premise177 : lowerHistoryPremises[176]? = some ([3, 6, 13, 21, 159, 260, 282, 287, 371, 387, 396, 419, 440, 602, 653, 725, 769, 784, 810, 811, 837, 843, 852, 856, 990, 1073, 1078, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 176 = 0+176 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 176 (by decide)]
  rfl
private theorem premise178 : lowerHistoryPremises[177]? = some ([3, 6, 13, 21, 159, 260, 282, 371, 387, 396, 419, 440, 602, 653, 725, 769, 784, 810, 837, 843, 856, 990, 1073, 1078, 1165] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 177 = 0+177 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 177 (by decide)]
  rfl
private theorem premise179 : lowerHistoryPremises[178]? = some ([3, 6, 13, 21, 179, 219, 237, 260, 282, 287, 371, 394, 419, 440, 657, 687, 728, 761, 769, 771, 784, 810, 811, 837, 843, 852, 856, 1026, 1114, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 178 = 0+178 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 178 (by decide)]
  rfl
private theorem premise180 : lowerHistoryPremises[179]? = some ([3, 6, 13, 21, 179, 219, 237, 260, 282, 371, 394, 419, 440, 657, 687, 728, 761, 769, 771, 784, 810, 837, 843, 856, 1026, 1114, 1165] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 179 = 0+179 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 179 (by decide)]
  rfl
private theorem premise181 : lowerHistoryPremises[180]? = some ([3, 6, 13, 21, 179, 219, 260, 282, 287, 371, 394, 419, 440, 657, 728, 769, 771, 784, 810, 811, 837, 843, 852, 856, 1026, 1105, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 180 = 0+180 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 180 (by decide)]
  rfl
private theorem premise182 : lowerHistoryPremises[181]? = some ([3, 6, 13, 21, 179, 219, 260, 282, 371, 394, 419, 440, 657, 728, 769, 771, 784, 810, 837, 843, 856, 1026, 1105, 1165] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 181 = 0+181 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 181 (by decide)]
  rfl
private theorem premise189 : lowerHistoryPremises[188]? = some ([3, 6, 13, 21, 196, 260, 282, 287, 371, 397, 403, 419, 440, 590, 609, 691, 769, 784, 810, 811, 837, 843, 852, 856, 969, 1039, 1078, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 188 = 0+188 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 188 (by decide)]
  rfl
private theorem premise190 : lowerHistoryPremises[189]? = some ([3, 6, 13, 21, 196, 260, 282, 371, 397, 403, 419, 440, 590, 609, 691, 769, 784, 810, 837, 843, 856, 969, 1039, 1078, 1165] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 189 = 0+189 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 189 (by decide)]
  rfl
private theorem premise203 : lowerHistoryPremises[202]? = some ([3, 6, 21, 244, 260, 282, 287, 371, 419, 440, 782, 784, 810, 811, 837, 843, 852, 853, 856, 1117, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 202 = 200+2 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 2 (by decide)]
  rfl
private theorem premise204 : lowerHistoryPremises[203]? = some ([3, 6, 21, 244, 260, 282, 371, 419, 440, 782, 784, 810, 837, 843, 853, 856, 1117, 1165] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 203 = 200+3 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 3 (by decide)]
  rfl
private theorem premise431 : lowerHistoryPremises[430]? = some ([3, 21, 244, 260, 270, 282, 286, 287, 371, 417, 419, 440, 782, 784, 805, 811, 831, 837, 843, 846, 852, 853, 856, 1117, 1173, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 430 = 400+30 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 30 (by decide)]
  rfl
private theorem premise432 : lowerHistoryPremises[431]? = some ([3, 21, 244, 260, 270, 282, 286, 371, 417, 419, 440, 782, 784, 805, 831, 837, 843, 846, 853, 856, 1117, 1165, 1173] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 431 = 400+31 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 31 (by decide)]
  rfl
private theorem premise433 : lowerHistoryPremises[432]? = some ([3, 21, 244, 260, 270, 282, 287, 371, 417, 419, 440, 782, 784, 811, 831, 837, 843, 852, 853, 856, 1117, 1164, 1181] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 432 = 400+32 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 32 (by decide)]
  rfl
private theorem premise434 : lowerHistoryPremises[433]? = some ([3, 21, 244, 260, 270, 282, 371, 417, 419, 440, 782, 784, 831, 837, 843, 853, 856, 1117, 1164, 1165] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 433 = 400+33 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 33 (by decide)]
  rfl
end BatchLookup17

open Freiman
namespace BatchFacts15

private theorem mapped_finset_congr (a b : List Nat) (f : Nat → CertBound)
    (h : a.toFinset = b.toFinset) :
    (a.map f).toFinset = (b.map f).toFinset := by
  have hm : ∀ x, x ∈ a ↔ x ∈ b := by
    intro x
    simpa only [List.mem_toFinset] using
      (Iff.of_eq (congrArg (fun s : Finset Nat => x ∈ s) h))
  ext x
  simp only [List.mem_toFinset, List.mem_map, hm]

private def extraBounds (p : LowerHistoryPath) (branch : Nat) : List CertBound :=
  let comp := (lowerHistoryEndpointComparisons p)[branch]?.getD ([],.automatic)
  comp.1 ++ (match comp.2 with | .bound b => [lowerHistoryComplement b] | _ => [])

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
private theorem extras : (List.range 16).map (extraBounds path) = expected := by
  decide +kernel
end ExtrasMemo17

open Freiman
namespace ExtraValues17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
end ExtraValues17

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

open Freiman BatchLookup17 BatchCoverage15
namespace BatchCoverageAll17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem coverage141 : (List.range path141.alternatives).all
    (coverageCheck path141 ([⟨.left,141,0,(-1),false,204,1004⟩,⟨.left,141,1,(-1),false,203,148⟩] : List LowerHistoryRecord)) = true := by
  decide +kernel
private theorem coverage142 : (List.range path142.alternatives).all
    (coverageCheck path142 ([⟨.left,142,0,(-1),false,190,870⟩,⟨.left,142,1,(-1),false,189,118⟩] : List LowerHistoryRecord)) = true := by
  decide +kernel
private theorem coverage143 : (List.range path143.alternatives).all
    (coverageCheck path143 ([⟨.left,143,0,(-1),false,178,900⟩,⟨.left,143,1,(-1),false,174,900⟩,⟨.left,143,2,(-1),false,176,900⟩,⟨.left,143,3,(-1),false,172,900⟩,⟨.left,143,4,(-1),false,177,124⟩,⟨.left,143,5,(-1),false,173,124⟩,⟨.left,143,6,(-1),false,175,124⟩,⟨.left,143,7,(-1),false,171,124⟩] : List LowerHistoryRecord)) = true := by
  decide +kernel
private theorem coverage144 : (List.range path144.alternatives).all
    (coverageCheck path144 ([⟨.left,144,0,(-1),false,182,942⟩,⟨.left,144,1,(-1),false,180,942⟩,⟨.left,144,2,(-1),false,181,130⟩,⟨.left,144,3,(-1),false,179,130⟩] : List LowerHistoryRecord)) = true := by
  decide +kernel
private theorem coverage145 : (List.range path145.alternatives).all
    (coverageCheck path145 ([⟨.left,145,0,(-1),false,434,1004⟩,⟨.left,145,1,(-1),false,432,65⟩,⟨.left,145,2,(-1),false,433,148⟩,⟨.left,145,3,(-1),false,431,148⟩] : List LowerHistoryRecord)) = true := by
  decide +kernel
end BatchCoverageAll17

open Freiman BatchLookup17
namespace PathLookup17
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem append5_get {α : Type} (a b c d e : Array α) (i : Nat)
    (h : i < a.size) : ((((a ++ b) ++ c) ++ d) ++ e)[i]? = a[i]? := by
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega)]
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega)]
  rw [Array.getElem?_append_left (by simp only [Array.size_append]; omega)]
  rw [Array.getElem?_append_left h]
private theorem sizeL : lowerHistoryPathsL.size = 594 := by rfl
private theorem first_lookup (i : Nat) (h : i < 594) :
    lowerHistoryPaths[i]? = lowerHistoryPathsL[i]? := by
  apply append5_get
  rwa [sizeL]
private theorem pathsL_slice : (lowerHistoryPathsL.toList.drop 100).take 50 = [
⟨.left,101,[2],([2],[3]),false,[(([3],[1]),false),(([3],[]),true),(([],[1]),false)],([2,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,102,[2],([2],[3]),false,[(([3],[1]),false),(([2],[]),true),(([],[1]),false)],([2,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,103,[2],([2],[3]),false,[(([3],[1]),false),(([1],[]),true),(([],[1]),false)],([2,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,104,[2],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([2,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,105,[2],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([1],[]),true)],([2,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,106,[2],([2],[3]),false,[(([2],[1]),true)],([2,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,107,[2],([2],[3]),false,[(([2],[1]),false),(([3],[]),true),(([],[1]),false)],([2,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,108,[2],([2],[3]),false,[(([2],[1]),false),(([2],[]),true),(([],[1]),false)],([2,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,109,[2],([2],[3]),false,[(([2],[1]),false),(([1],[]),true),(([],[1]),false)],([2,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,110,[2],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([3],[]),true)],([2,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,111,[2],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true)],([2,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,112,[2],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true)],([2,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,113,[2],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([2,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,114,[2],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([2,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,115,[2],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,3,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,116,[2],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,3,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,117,[2],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,3,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,118,[2],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([2,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,119,[2],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([2,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,120,[2],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([2,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,121,[2],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([2,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,122,[2],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([2,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,123,[2],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([2,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,124,[2],([2],[3]),false,[(([3],[]),true),(([1],[]),false)],([2,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,125,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([2,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,126,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([2,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,127,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([2,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,128,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,2,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,129,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,16⟩,
⟨.left,130,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,2,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,8⟩,
⟨.left,131,[2],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([2,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,8⟩,
⟨.left,132,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([2,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,133,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([2,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,8⟩,
⟨.left,134,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([2,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,135,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([2,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,136,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([2,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,137,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([2,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,138,[2],([2],[3]),false,[(([2],[]),true),(([1],[]),false)],([2,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,139,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([2,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,140,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([2,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,141,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,142,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,143,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,8⟩,
⟨.left,144,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,145,[2],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,146,[2],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([2,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,147,[2],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([2,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,148,[2],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,149,[2],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([2,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,150,[2],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([2,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
] := by rfl
private theorem slice_get {α : Type} (xs : List α) (i : Nat) (hi : i < 50) :
    ((xs.drop 100).take 50)[i]? = xs[100+i]? := by
  simp [List.getElem?_take, List.getElem?_drop, hi]
private theorem path141_lookup : lowerHistoryPaths[140]? = some path141 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[40]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[140]? = some path141 :=
    (slice_get lowerHistoryPathsL.toList 40 (by decide)).symm.trans hs
  exact (first_lookup 140 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path142_lookup : lowerHistoryPaths[141]? = some path142 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[41]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[141]? = some path142 :=
    (slice_get lowerHistoryPathsL.toList 41 (by decide)).symm.trans hs
  exact (first_lookup 141 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path143_lookup : lowerHistoryPaths[142]? = some path143 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[42]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[142]? = some path143 :=
    (slice_get lowerHistoryPathsL.toList 42 (by decide)).symm.trans hs
  exact (first_lookup 142 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path144_lookup : lowerHistoryPaths[143]? = some path144 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[43]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[143]? = some path144 :=
    (slice_get lowerHistoryPathsL.toList 43 (by decide)).symm.trans hs
  exact (first_lookup 143 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path145_lookup : lowerHistoryPaths[144]? = some path145 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[44]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[144]? = some path145 :=
    (slice_get lowerHistoryPathsL.toList 44 (by decide)).symm.trans hs
  exact (first_lookup 144 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
end PathLookup17

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
private theorem witness65_projection :
    (lowerHistoryWitness 65).lowerBound = lowerHistoryBound 286 ∧
    (lowerHistoryWitness 65).upperBound = lowerHistoryBound 1117 ∧
    (lowerHistoryWitness 65).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[64]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 286, lowerHistoryBound 1117, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 286, lowerHistoryBound 1117, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk1 64 (by decide))).trans hl
private theorem witness118_projection :
    (lowerHistoryWitness 118).lowerBound = lowerHistoryBound 287 ∧
    (lowerHistoryWitness 118).upperBound = lowerHistoryBound 969 ∧
    (lowerHistoryWitness 118).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[117]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 969, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 969, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk1 117 (by decide))).trans hl
private theorem witness124_projection :
    (lowerHistoryWitness 124).lowerBound = lowerHistoryBound 287 ∧
    (lowerHistoryWitness 124).upperBound = lowerHistoryBound 990 ∧
    (lowerHistoryWitness 124).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[123]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 990, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 990, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk1 123 (by decide))).trans hl
private theorem witness130_projection :
    (lowerHistoryWitness 130).lowerBound = lowerHistoryBound 287 ∧
    (lowerHistoryWitness 130).upperBound = lowerHistoryBound 1026 ∧
    (lowerHistoryWitness 130).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[129]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 1026, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 1026, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk1 129 (by decide))).trans hl
private theorem witness148_projection :
    (lowerHistoryWitness 148).lowerBound = lowerHistoryBound 287 ∧
    (lowerHistoryWitness 148).upperBound = lowerHistoryBound 1117 ∧
    (lowerHistoryWitness 148).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses01[147]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 287, lowerHistoryBound 1117, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 287, lowerHistoryBound 1117, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk1 147 (by decide))).trans hl
private theorem witness870_projection :
    (lowerHistoryWitness 870).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 870).upperBound = lowerHistoryBound 969 ∧
    (lowerHistoryWitness 870).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[69]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 969, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 969, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk5 69 (by decide))).trans hl
private theorem witness900_projection :
    (lowerHistoryWitness 900).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 900).upperBound = lowerHistoryBound 990 ∧
    (lowerHistoryWitness 900).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[99]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 990, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 990, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk5 99 (by decide))).trans hl
private theorem witness942_projection :
    (lowerHistoryWitness 942).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 942).upperBound = lowerHistoryBound 1026 ∧
    (lowerHistoryWitness 942).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[141]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 1026, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 1026, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk5 141 (by decide))).trans hl
private theorem witness1004_projection :
    (lowerHistoryWitness 1004).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 1004).upperBound = lowerHistoryBound 1117 ∧
    (lowerHistoryWitness 1004).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[3]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 1117, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 1117, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 3)).trans hl
end WitnessLookup17

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

open Freiman BatchLookup17 BindingIds19
namespace BatchIdSolution100
set_option maxRecDepth 30000
set_option maxHeartbeats 0
private theorem premise_size : lowerHistoryPremises.size = 1025 := by
  simp only [lowerHistoryPremises, Array.size_append]
  rfl
private theorem witness_size : lowerHistoryWitnesses.size = 1194 := by
  simp only [lowerHistoryWitnesses, Array.size_append]
  rfl
private def wids : Nat → Nat × Nat
  | 3 => (277,836)
  | 6 => (277,892)
  | 10 => (277,1139)
  | 13 => (277,1153)
  | 35 => (285,836)
  | 39 => (285,879)
  | 43 => (285,891)
  | 49 => (285,1139)
  | 65 => (286,1117)
  | 118 => (287,969)
  | 124 => (287,990)
  | 130 => (287,1026)
  | 136 => (287,1064)
  | 142 => (287,1086)
  | 148 => (287,1117)
  | 265 => (295,836)
  | 269 => (295,883)
  | 273 => (295,894)
  | 279 => (295,1139)
  | 305 => (429,881)
  | 565 => (439,836)
  | 569 => (439,881)
  | 573 => (439,892)
  | 579 => (439,1139)
  | 816 => (440,929)
  | 822 => (440,942)
  | 828 => (440,943)
  | 846 => (440,957)
  | 858 => (440,965)
  | 870 => (440,969)
  | 882 => (440,984)
  | 888 => (440,986)
  | 900 => (440,990)
  | 912 => (440,1016)
  | 924 => (440,1020)
  | 930 => (440,1021)
  | 936 => (440,1022)
  | 942 => (440,1026)
  | 954 => (440,1048)
  | 960 => (440,1051)
  | 966 => (440,1064)
  | 972 => (440,1065)
  | 978 => (440,1071)
  | 984 => (440,1086)
  | 990 => (440,1087)
  | 996 => (440,1093)
  | 1004 => (440,1117)
  | 1023 => (440,1142)
  | 1131 => (442,984)
  | 1137 => (442,1016)
  | 1143 => (442,1020)
  | 1149 => (442,1021)
  | 1155 => (442,1022)
  | 1161 => (442,1048)
  | 1167 => (442,1051)
  | 1173 => (442,1065)
  | 1179 => (442,1087)
  | 1191 => (442,1156)
  | _ => (0,0)
private def preIDs : Nat → List Nat
  | 21 => [2, 3, 6, 21, 225, 260, 282, 371, 410, 440, 724, 810, 822, 825, 837, 843, 851, 856, 1086, 1148]
  | 22 => [2, 3, 6, 21, 234, 260, 282, 371, 413, 440, 689, 802, 810, 825, 837, 843, 851, 856, 1064, 1120, 1129, 1148]
  | 37 => [2, 3, 21, 236, 260, 266, 274, 282, 371, 414, 418, 440, 747, 763, 779, 813, 829, 837, 843, 851, 856, 878, 1093, 1155]
  | 38 => [2, 3, 21, 236, 260, 266, 282, 371, 414, 418, 440, 747, 763, 779, 813, 829, 837, 843, 851, 856, 1093, 1152, 1155]
  | 39 => [2, 3, 21, 236, 260, 274, 282, 371, 414, 418, 440, 747, 779, 829, 837, 843, 851, 856, 878, 1093, 1145]
  | 40 => [2, 3, 21, 236, 260, 282, 371, 414, 418, 440, 747, 779, 829, 837, 843, 851, 856, 1093, 1145, 1152]
  | 41 => [2, 3, 21, 244, 260, 270, 282, 286, 371, 417, 440, 782, 805, 831, 837, 843, 846, 851, 853, 856, 1117, 1173]
  | 42 => [2, 3, 21, 244, 260, 270, 282, 371, 417, 440, 782, 831, 837, 843, 851, 853, 856, 1117, 1164]
  | 55 => [2, 3, 21, 260, 262, 282, 371, 423, 426, 440, 736, 752, 809, 837, 843, 851, 856, 1071, 1132, 1152]
  | 92 => [3, 5, 8, 21, 201, 260, 275, 371, 400, 420, 440, 664, 780, 781, 790, 791, 817, 843, 856, 876, 1051, 1122]
  | 93 => [3, 5, 8, 21, 201, 260, 275, 371, 400, 440, 442, 664, 781, 790, 791, 817, 843, 856, 1051, 1122]
  | 94 => [3, 5, 8, 21, 201, 260, 371, 400, 420, 440, 664, 780, 781, 790, 791, 817, 843, 856, 1051, 1122, 1153]
  | 95 => [3, 5, 8, 21, 224, 260, 275, 371, 420, 440, 738, 780, 781, 817, 823, 843, 856, 876, 1087]
  | 96 => [3, 5, 8, 21, 224, 260, 275, 371, 440, 442, 738, 781, 817, 823, 843, 856, 1087]
  | 97 => [3, 5, 8, 21, 224, 260, 371, 420, 440, 738, 780, 781, 817, 823, 843, 856, 1087, 1153]
  | 98 => [3, 5, 8, 21, 232, 260, 275, 371, 412, 420, 440, 631, 764, 780, 781, 791, 817, 843, 856, 876, 1021, 1091, 1103, 1122]
  | 99 => [3, 5, 8, 21, 232, 260, 275, 371, 412, 440, 442, 631, 764, 781, 791, 817, 843, 856, 1021, 1091, 1103, 1122]
  | 100 => [3, 5, 8, 21, 232, 260, 371, 412, 420, 440, 631, 764, 780, 781, 791, 817, 843, 856, 1021, 1091, 1103, 1122, 1153]
  | 104 => [3, 5, 21, 205, 243, 250, 260, 275, 371, 402, 411, 420, 440, 693, 704, 734, 775, 780, 787, 817, 843, 856, 868, 876, 1048, 1134]
  | 105 => [3, 5, 21, 205, 243, 250, 260, 275, 371, 402, 411, 440, 442, 693, 704, 734, 775, 787, 817, 843, 856, 868, 1048, 1134]
  | 106 => [3, 5, 21, 205, 243, 250, 260, 371, 402, 411, 420, 440, 693, 704, 734, 775, 780, 787, 817, 843, 856, 868, 1048, 1134, 1153]
  | 107 => [3, 5, 21, 205, 243, 260, 275, 371, 402, 411, 420, 440, 693, 704, 734, 775, 780, 787, 817, 843, 856, 876, 1048, 1125, 1134]
  | 108 => [3, 5, 21, 205, 243, 260, 275, 371, 402, 411, 440, 442, 693, 704, 734, 775, 787, 817, 843, 856, 1048, 1125, 1134]
  | 109 => [3, 5, 21, 205, 243, 260, 371, 402, 411, 420, 440, 693, 704, 734, 775, 780, 787, 817, 843, 856, 1048, 1125, 1134, 1153]
  | 110 => [3, 5, 21, 205, 250, 260, 275, 371, 402, 411, 420, 440, 693, 734, 780, 787, 817, 843, 856, 868, 876, 1048, 1113]
  | 111 => [3, 5, 21, 205, 250, 260, 275, 371, 402, 411, 440, 442, 693, 734, 787, 817, 843, 856, 868, 1048, 1113]
  | 112 => [3, 5, 21, 205, 250, 260, 371, 402, 411, 420, 440, 693, 734, 780, 787, 817, 843, 856, 868, 1048, 1113, 1153]
  | 113 => [3, 5, 21, 205, 260, 275, 371, 402, 411, 420, 440, 693, 734, 780, 787, 817, 843, 856, 876, 1048, 1113, 1125]
  | 114 => [3, 5, 21, 205, 260, 275, 371, 402, 411, 440, 442, 693, 734, 787, 817, 843, 856, 1048, 1113, 1125]
  | 115 => [3, 5, 21, 205, 260, 371, 402, 411, 420, 440, 693, 734, 780, 787, 817, 843, 856, 1048, 1113, 1125, 1153]
  | 116 => [3, 5, 21, 212, 260, 275, 371, 407, 408, 420, 440, 675, 695, 758, 780, 817, 843, 856, 876, 1020, 1096, 1125]
  | 117 => [3, 5, 21, 212, 260, 275, 371, 407, 408, 440, 442, 675, 695, 758, 817, 843, 856, 1020, 1096, 1125]
  | 118 => [3, 5, 21, 212, 260, 371, 407, 408, 420, 440, 675, 695, 758, 780, 817, 843, 856, 1020, 1096, 1125, 1153]
  | 122 => [3, 5, 21, 224, 256, 260, 265, 275, 371, 409, 420, 440, 738, 768, 780, 801, 815, 817, 823, 843, 856, 876, 1087, 1154]
  | 123 => [3, 5, 21, 224, 256, 260, 265, 275, 371, 409, 440, 442, 738, 768, 801, 815, 817, 823, 843, 856, 1087, 1154]
  | 124 => [3, 5, 21, 224, 256, 260, 265, 371, 409, 420, 440, 738, 768, 780, 801, 815, 817, 823, 843, 856, 1087, 1153, 1154]
  | 125 => [3, 5, 21, 224, 256, 260, 275, 371, 409, 420, 440, 738, 780, 801, 817, 823, 843, 856, 876, 1087, 1144]
  | 126 => [3, 5, 21, 224, 256, 260, 275, 371, 409, 440, 442, 738, 801, 817, 823, 843, 856, 1087, 1144]
  | 127 => [3, 5, 21, 224, 256, 260, 371, 409, 420, 440, 738, 780, 801, 817, 823, 843, 856, 1087, 1144, 1153]
  | 171 => [3, 6, 13, 21, 159, 215, 220, 260, 282, 287, 371, 387, 396, 419, 440, 602, 616, 653, 706, 725, 769, 784, 810, 811, 837, 843, 852, 856, 869, 990, 1082, 1181]
  | 172 => [3, 6, 13, 21, 159, 215, 220, 260, 282, 371, 387, 396, 419, 440, 602, 616, 653, 706, 725, 769, 784, 810, 837, 843, 856, 869, 990, 1082, 1165]
  | 173 => [3, 6, 13, 21, 159, 215, 260, 282, 287, 371, 387, 396, 419, 440, 602, 616, 653, 706, 725, 769, 784, 810, 811, 837, 843, 852, 856, 990, 1078, 1082, 1181]
  | 174 => [3, 6, 13, 21, 159, 215, 260, 282, 371, 387, 396, 419, 440, 602, 616, 653, 706, 725, 769, 784, 810, 837, 843, 856, 990, 1078, 1082, 1165]
  | 175 => [3, 6, 13, 21, 159, 220, 260, 282, 287, 371, 387, 396, 419, 440, 602, 653, 725, 769, 784, 810, 811, 837, 843, 852, 856, 869, 990, 1073, 1181]
  | 176 => [3, 6, 13, 21, 159, 220, 260, 282, 371, 387, 396, 419, 440, 602, 653, 725, 769, 784, 810, 837, 843, 856, 869, 990, 1073, 1165]
  | 177 => [3, 6, 13, 21, 159, 260, 282, 287, 371, 387, 396, 419, 440, 602, 653, 725, 769, 784, 810, 811, 837, 843, 852, 856, 990, 1073, 1078, 1181]
  | 178 => [3, 6, 13, 21, 159, 260, 282, 371, 387, 396, 419, 440, 602, 653, 725, 769, 784, 810, 837, 843, 856, 990, 1073, 1078, 1165]
  | 179 => [3, 6, 13, 21, 179, 219, 237, 260, 282, 287, 371, 394, 419, 440, 657, 687, 728, 761, 769, 771, 784, 810, 811, 837, 843, 852, 856, 1026, 1114, 1181]
  | 180 => [3, 6, 13, 21, 179, 219, 237, 260, 282, 371, 394, 419, 440, 657, 687, 728, 761, 769, 771, 784, 810, 837, 843, 856, 1026, 1114, 1165]
  | 181 => [3, 6, 13, 21, 179, 219, 260, 282, 287, 371, 394, 419, 440, 657, 728, 769, 771, 784, 810, 811, 837, 843, 852, 856, 1026, 1105, 1181]
  | 182 => [3, 6, 13, 21, 179, 219, 260, 282, 371, 394, 419, 440, 657, 728, 769, 771, 784, 810, 837, 843, 856, 1026, 1105, 1165]
  | 189 => [3, 6, 13, 21, 196, 260, 282, 287, 371, 397, 403, 419, 440, 590, 609, 691, 769, 784, 810, 811, 837, 843, 852, 856, 969, 1039, 1078, 1181]
  | 190 => [3, 6, 13, 21, 196, 260, 282, 371, 397, 403, 419, 440, 590, 609, 691, 769, 784, 810, 837, 843, 856, 969, 1039, 1078, 1165]
  | 199 => [3, 6, 21, 225, 260, 282, 287, 371, 410, 419, 440, 724, 784, 810, 811, 822, 825, 837, 843, 852, 856, 1086, 1148, 1181]
  | 200 => [3, 6, 21, 225, 260, 282, 371, 410, 419, 440, 724, 784, 810, 822, 825, 837, 843, 856, 1086, 1148, 1165]
  | 201 => [3, 6, 21, 234, 260, 282, 287, 371, 413, 419, 440, 689, 784, 802, 810, 811, 825, 837, 843, 852, 856, 1064, 1120, 1129, 1148, 1181]
  | 202 => [3, 6, 21, 234, 260, 282, 371, 413, 419, 440, 689, 784, 802, 810, 825, 837, 843, 856, 1064, 1120, 1129, 1148, 1165]
  | 203 => [3, 6, 21, 244, 260, 282, 287, 371, 419, 440, 782, 784, 810, 811, 837, 843, 852, 853, 856, 1117, 1181]
  | 204 => [3, 6, 21, 244, 260, 282, 371, 419, 440, 782, 784, 810, 837, 843, 853, 856, 1117, 1165]
  | 207 => [3, 7, 19, 21, 178, 260, 275, 371, 393, 440, 442, 621, 766, 767, 807, 814, 843, 856, 1022, 1106]
  | 208 => [3, 7, 19, 21, 178, 260, 371, 393, 425, 440, 621, 751, 766, 767, 807, 814, 843, 856, 1022, 1106, 1153]
  | 209 => [3, 7, 19, 21, 207, 260, 275, 371, 440, 442, 699, 803, 807, 814, 843, 856, 1065]
  | 210 => [3, 7, 19, 21, 207, 260, 371, 425, 440, 699, 751, 803, 807, 814, 843, 856, 1065, 1153]
  | 213 => [3, 7, 21, 176, 230, 239, 260, 275, 371, 391, 406, 440, 442, 646, 658, 697, 740, 754, 814, 843, 850, 856, 1016, 1111]
  | 214 => [3, 7, 21, 176, 230, 239, 260, 371, 391, 406, 425, 440, 646, 658, 697, 740, 751, 754, 814, 843, 850, 856, 1016, 1111, 1153]
  | 215 => [3, 7, 21, 176, 230, 260, 275, 371, 391, 406, 440, 442, 646, 658, 697, 740, 754, 814, 843, 856, 1016, 1107, 1111]
  | 216 => [3, 7, 21, 176, 230, 260, 371, 391, 406, 425, 440, 646, 658, 697, 740, 751, 754, 814, 843, 856, 1016, 1107, 1111, 1153]
  | 217 => [3, 7, 21, 176, 239, 260, 275, 371, 391, 406, 440, 442, 646, 697, 754, 814, 843, 850, 856, 1016, 1094]
  | 218 => [3, 7, 21, 176, 239, 260, 371, 391, 406, 425, 440, 646, 697, 751, 754, 814, 843, 850, 856, 1016, 1094, 1153]
  | 219 => [3, 7, 21, 176, 260, 275, 371, 391, 406, 440, 442, 646, 697, 754, 814, 843, 856, 1016, 1094, 1107]
  | 220 => [3, 7, 21, 176, 260, 371, 391, 406, 425, 440, 646, 697, 751, 754, 814, 843, 856, 1016, 1094, 1107, 1153]
  | 221 => [3, 7, 21, 177, 260, 275, 371, 392, 399, 440, 442, 627, 650, 718, 814, 843, 856, 984, 1067, 1107]
  | 222 => [3, 7, 21, 177, 260, 371, 392, 399, 425, 440, 627, 650, 718, 751, 814, 843, 856, 984, 1067, 1107, 1153]
  | 225 => [3, 7, 21, 207, 251, 260, 264, 275, 371, 404, 440, 442, 699, 729, 788, 793, 803, 814, 843, 856, 1065, 1143]
  | 226 => [3, 7, 21, 207, 251, 260, 264, 371, 404, 425, 440, 699, 729, 751, 788, 793, 803, 814, 843, 856, 1065, 1143, 1153]
  | 227 => [3, 7, 21, 207, 260, 264, 275, 371, 404, 440, 442, 699, 788, 803, 814, 843, 856, 1065, 1126]
  | 228 => [3, 7, 21, 207, 260, 264, 371, 404, 425, 440, 699, 751, 788, 803, 814, 843, 856, 1065, 1126, 1153]
  | 237 => [3, 8, 21, 34, 136, 180, 191, 260, 267, 275, 371, 376, 385, 416, 420, 440, 545, 560, 591, 649, 663, 711, 746, 772, 780, 781, 821, 843, 845, 856, 876, 957, 1046, 1157]
  | 238 => [3, 8, 21, 34, 136, 180, 191, 260, 267, 371, 376, 385, 416, 420, 440, 545, 560, 591, 649, 663, 711, 746, 772, 780, 781, 821, 843, 845, 856, 957, 1046, 1153, 1157]
  | 239 => [3, 8, 21, 34, 136, 180, 191, 260, 275, 371, 376, 385, 416, 420, 440, 545, 560, 591, 649, 663, 711, 746, 780, 781, 843, 845, 856, 876, 957, 1046, 1146]
  | 240 => [3, 8, 21, 34, 136, 180, 191, 260, 371, 376, 385, 416, 420, 440, 545, 560, 591, 649, 663, 711, 746, 780, 781, 843, 845, 856, 957, 1046, 1146, 1153]
  | 241 => [3, 8, 21, 34, 136, 180, 260, 267, 275, 371, 376, 385, 416, 420, 440, 545, 560, 591, 649, 663, 711, 746, 772, 780, 781, 821, 843, 856, 876, 957, 1037, 1046, 1157]
  | 242 => [3, 8, 21, 34, 136, 180, 260, 267, 371, 376, 385, 416, 420, 440, 545, 560, 591, 649, 663, 711, 746, 772, 780, 781, 821, 843, 856, 957, 1037, 1046, 1153, 1157]
  | 243 => [3, 8, 21, 34, 136, 180, 260, 275, 371, 376, 385, 416, 420, 440, 545, 560, 591, 649, 663, 711, 746, 780, 781, 843, 856, 876, 957, 1037, 1046, 1146]
  | 244 => [3, 8, 21, 34, 136, 180, 260, 371, 376, 385, 416, 420, 440, 545, 560, 591, 649, 663, 711, 746, 780, 781, 843, 856, 957, 1037, 1046, 1146, 1153]
  | 245 => [3, 8, 21, 34, 136, 191, 260, 267, 275, 371, 376, 385, 416, 420, 440, 545, 591, 663, 711, 746, 772, 780, 781, 821, 843, 845, 856, 876, 957, 1025, 1157]
  | 246 => [3, 8, 21, 34, 136, 191, 260, 267, 371, 376, 385, 416, 420, 440, 545, 591, 663, 711, 746, 772, 780, 781, 821, 843, 845, 856, 957, 1025, 1153, 1157]
  | 247 => [3, 8, 21, 34, 136, 191, 260, 275, 371, 376, 385, 416, 420, 440, 545, 591, 663, 711, 746, 780, 781, 843, 845, 856, 876, 957, 1025, 1146]
  | 248 => [3, 8, 21, 34, 136, 191, 260, 371, 376, 385, 416, 420, 440, 545, 591, 663, 711, 746, 780, 781, 843, 845, 856, 957, 1025, 1146, 1153]
  | 249 => [3, 8, 21, 34, 136, 260, 267, 275, 371, 376, 385, 416, 420, 440, 545, 591, 663, 711, 746, 772, 780, 781, 821, 843, 856, 876, 957, 1025, 1037, 1157]
  | 250 => [3, 8, 21, 34, 136, 260, 267, 371, 376, 385, 416, 420, 440, 545, 591, 663, 711, 746, 772, 780, 781, 821, 843, 856, 957, 1025, 1037, 1153, 1157]
  | 251 => [3, 8, 21, 34, 136, 260, 275, 371, 376, 385, 416, 420, 440, 545, 591, 663, 711, 746, 780, 781, 843, 856, 876, 957, 1025, 1037, 1146]
  | 252 => [3, 8, 21, 34, 136, 260, 371, 376, 385, 416, 420, 440, 545, 591, 663, 711, 746, 780, 781, 843, 856, 957, 1025, 1037, 1146, 1153]
  | 253 => [3, 8, 21, 34, 149, 186, 214, 260, 267, 275, 371, 382, 416, 420, 440, 594, 619, 670, 708, 711, 719, 746, 772, 780, 781, 821, 843, 856, 876, 986, 1081, 1157]
  | 254 => [3, 8, 21, 34, 149, 186, 214, 260, 267, 371, 382, 416, 420, 440, 594, 619, 670, 708, 711, 719, 746, 772, 780, 781, 821, 843, 856, 986, 1081, 1153, 1157]
  | 255 => [3, 8, 21, 34, 149, 186, 214, 260, 275, 371, 382, 416, 420, 440, 594, 619, 670, 708, 711, 719, 746, 780, 781, 843, 856, 876, 986, 1081, 1146]
  | 256 => [3, 8, 21, 34, 149, 186, 214, 260, 371, 382, 416, 420, 440, 594, 619, 670, 708, 711, 719, 746, 780, 781, 843, 856, 986, 1081, 1146, 1153]
  | 257 => [3, 8, 21, 34, 149, 186, 260, 267, 275, 371, 382, 416, 420, 440, 594, 670, 711, 719, 746, 772, 780, 781, 821, 843, 856, 876, 986, 1072, 1157]
  | 258 => [3, 8, 21, 34, 149, 186, 260, 267, 371, 382, 416, 420, 440, 594, 670, 711, 719, 746, 772, 780, 781, 821, 843, 856, 986, 1072, 1153, 1157]
  | 259 => [3, 8, 21, 34, 149, 186, 260, 275, 371, 382, 416, 420, 440, 594, 670, 711, 719, 746, 780, 781, 843, 856, 876, 986, 1072, 1146]
  | 260 => [3, 8, 21, 34, 149, 186, 260, 371, 382, 416, 420, 440, 594, 670, 711, 719, 746, 780, 781, 843, 856, 986, 1072, 1146, 1153]
  | 261 => [3, 8, 21, 34, 153, 260, 267, 275, 371, 384, 389, 416, 420, 440, 535, 548, 624, 711, 746, 772, 780, 781, 821, 843, 856, 876, 943, 995, 1037, 1157]
  | 262 => [3, 8, 21, 34, 153, 260, 267, 371, 384, 389, 416, 420, 440, 535, 548, 624, 711, 746, 772, 780, 781, 821, 843, 856, 943, 995, 1037, 1153, 1157]
  | 263 => [3, 8, 21, 34, 153, 260, 275, 371, 384, 389, 416, 420, 440, 535, 548, 624, 711, 746, 780, 781, 843, 856, 876, 943, 995, 1037, 1146]
  | 264 => [3, 8, 21, 34, 153, 260, 371, 384, 389, 416, 420, 440, 535, 548, 624, 711, 746, 780, 781, 843, 856, 943, 995, 1037, 1146, 1153]
  | 285 => [3, 8, 21, 201, 260, 267, 275, 371, 400, 416, 420, 440, 664, 746, 772, 780, 781, 790, 791, 821, 843, 856, 876, 1051, 1122, 1157]
  | 286 => [3, 8, 21, 201, 260, 267, 371, 400, 416, 420, 440, 664, 746, 772, 780, 781, 790, 791, 821, 843, 856, 1051, 1122, 1153, 1157]
  | 287 => [3, 8, 21, 201, 260, 275, 371, 400, 416, 420, 440, 664, 746, 780, 781, 790, 791, 843, 856, 876, 1051, 1122, 1146]
  | 288 => [3, 8, 21, 201, 260, 371, 400, 416, 420, 440, 664, 746, 780, 781, 790, 791, 843, 856, 1051, 1122, 1146, 1153]
  | 289 => [3, 8, 21, 224, 260, 267, 275, 371, 416, 420, 440, 738, 746, 772, 780, 781, 821, 823, 843, 856, 876, 1087, 1157]
  | 290 => [3, 8, 21, 224, 260, 267, 371, 416, 420, 440, 738, 746, 772, 780, 781, 821, 823, 843, 856, 1087, 1153, 1157]
  | 291 => [3, 8, 21, 224, 260, 275, 371, 416, 420, 440, 738, 746, 780, 781, 823, 843, 856, 876, 1087, 1146]
  | 292 => [3, 8, 21, 224, 260, 371, 416, 420, 440, 738, 746, 780, 781, 823, 843, 856, 1087, 1146, 1153]
  | 293 => [3, 8, 21, 232, 260, 267, 275, 371, 412, 416, 420, 440, 631, 746, 764, 772, 780, 781, 791, 821, 843, 856, 876, 1021, 1091, 1103, 1122, 1157]
  | 294 => [3, 8, 21, 232, 260, 267, 371, 412, 416, 420, 440, 631, 746, 764, 772, 780, 781, 791, 821, 843, 856, 1021, 1091, 1103, 1122, 1153, 1157]
  | 295 => [3, 8, 21, 232, 260, 275, 371, 412, 416, 420, 440, 631, 746, 764, 780, 781, 791, 843, 856, 876, 1021, 1091, 1103, 1122, 1146]
  | 296 => [3, 8, 21, 232, 260, 371, 412, 416, 420, 440, 631, 746, 764, 780, 781, 791, 843, 856, 1021, 1091, 1103, 1122, 1146, 1153]
  | 333 => [3, 19, 21, 44, 127, 156, 170, 260, 371, 372, 378, 422, 425, 440, 518, 527, 547, 599, 618, 665, 735, 751, 807, 820, 843, 856, 942, 1014, 1131, 1153]
  | 334 => [3, 19, 21, 44, 127, 156, 260, 371, 372, 378, 422, 425, 440, 518, 527, 547, 599, 618, 665, 735, 751, 807, 843, 856, 942, 1007, 1014, 1131, 1153]
  | 335 => [3, 19, 21, 44, 127, 170, 260, 371, 372, 378, 422, 425, 440, 518, 547, 618, 665, 735, 751, 807, 820, 843, 856, 942, 993, 1131, 1153]
  | 336 => [3, 19, 21, 44, 127, 260, 371, 372, 378, 422, 425, 440, 518, 547, 618, 665, 735, 751, 807, 843, 856, 942, 993, 1007, 1131, 1153]
  | 337 => [3, 19, 21, 44, 133, 168, 189, 260, 371, 374, 422, 425, 440, 552, 582, 636, 662, 665, 685, 735, 751, 807, 843, 856, 965, 1060, 1131, 1153]
  | 338 => [3, 19, 21, 44, 133, 168, 260, 371, 374, 422, 425, 440, 552, 636, 665, 685, 735, 751, 807, 843, 856, 965, 1035, 1131, 1153]
  | 339 => [3, 19, 21, 44, 135, 260, 371, 375, 380, 422, 425, 440, 509, 521, 583, 665, 735, 751, 807, 843, 856, 929, 971, 1007, 1131, 1153]
  | 345 => [3, 19, 21, 178, 260, 371, 393, 422, 425, 440, 621, 735, 751, 766, 767, 807, 843, 856, 1022, 1106, 1131, 1153]
  | 346 => [3, 19, 21, 207, 260, 371, 422, 425, 440, 699, 735, 751, 803, 807, 843, 856, 1065, 1131, 1153]
  | 421 => [3, 21, 207, 251, 260, 264, 371, 404, 422, 425, 440, 699, 729, 735, 751, 788, 793, 803, 843, 856, 1065, 1131, 1143, 1153]
  | 422 => [3, 21, 207, 260, 264, 371, 404, 422, 425, 440, 699, 735, 751, 788, 803, 843, 856, 1065, 1126, 1131, 1153]
  | 423 => [3, 21, 224, 256, 260, 265, 267, 275, 371, 409, 416, 420, 440, 738, 746, 768, 772, 780, 801, 815, 821, 823, 843, 856, 876, 1087, 1154, 1157]
  | 424 => [3, 21, 224, 256, 260, 265, 267, 371, 409, 416, 420, 440, 738, 746, 768, 772, 780, 801, 815, 821, 823, 843, 856, 1087, 1153, 1154, 1157]
  | 425 => [3, 21, 224, 256, 260, 265, 275, 371, 409, 416, 420, 440, 738, 746, 768, 780, 801, 815, 823, 843, 856, 876, 1087, 1146, 1154]
  | 426 => [3, 21, 224, 256, 260, 265, 371, 409, 416, 420, 440, 738, 746, 768, 780, 801, 815, 823, 843, 856, 1087, 1146, 1153, 1154]
  | 427 => [3, 21, 224, 256, 260, 267, 275, 371, 409, 416, 420, 440, 738, 746, 772, 780, 801, 821, 823, 843, 856, 876, 1087, 1144, 1157]
  | 428 => [3, 21, 224, 256, 260, 267, 371, 409, 416, 420, 440, 738, 746, 772, 780, 801, 821, 823, 843, 856, 1087, 1144, 1153, 1157]
  | 429 => [3, 21, 224, 256, 260, 275, 371, 409, 416, 420, 440, 738, 746, 780, 801, 823, 843, 856, 876, 1087, 1144, 1146]
  | 430 => [3, 21, 224, 256, 260, 371, 409, 416, 420, 440, 738, 746, 780, 801, 823, 843, 856, 1087, 1144, 1146, 1153]
  | 431 => [3, 21, 244, 260, 270, 282, 286, 287, 371, 417, 419, 440, 782, 784, 805, 811, 831, 837, 843, 846, 852, 853, 856, 1117, 1173, 1181]
  | 432 => [3, 21, 244, 260, 270, 282, 286, 371, 417, 419, 440, 782, 784, 805, 831, 837, 843, 846, 853, 856, 1117, 1165, 1173]
  | 433 => [3, 21, 244, 260, 270, 282, 287, 371, 417, 419, 440, 782, 784, 811, 831, 837, 843, 852, 853, 856, 1117, 1164, 1181]
  | 434 => [3, 21, 244, 260, 270, 282, 371, 417, 419, 440, 782, 784, 831, 837, 843, 853, 856, 1117, 1164, 1165]
  | 450 => [3, 21, 259, 260, 275, 277, 285, 371, 420, 440, 780, 827, 836, 843, 856, 863, 870, 876, 1156, 1182]
  | 451 => [3, 21, 259, 260, 275, 277, 295, 371, 420, 439, 440, 780, 827, 836, 843, 856, 870, 876, 1156, 1184]
  | 452 => [3, 21, 259, 260, 275, 277, 295, 371, 420, 440, 780, 827, 836, 843, 855, 856, 870, 876, 1156, 1183]
  | 453 => [3, 21, 259, 260, 275, 277, 371, 420, 440, 780, 827, 836, 843, 856, 863, 870, 876, 1156, 1161, 1184]
  | 495 => [3, 21, 260, 275, 277, 284, 285, 371, 420, 429, 440, 780, 827, 843, 856, 863, 870, 876, 879, 1156]
  | 496 => [3, 21, 260, 275, 277, 284, 285, 371, 420, 440, 780, 819, 827, 843, 856, 863, 870, 876, 891, 1156]
  | 497 => [3, 21, 260, 275, 277, 284, 295, 371, 420, 429, 439, 440, 780, 827, 843, 856, 870, 876, 881, 1156]
  | 498 => [3, 21, 260, 275, 277, 284, 295, 371, 420, 429, 440, 780, 827, 843, 855, 856, 870, 876, 883, 1156]
  | 499 => [3, 21, 260, 275, 277, 284, 295, 371, 420, 439, 440, 780, 819, 827, 843, 856, 870, 876, 892, 1156]
  | 500 => [3, 21, 260, 275, 277, 284, 295, 371, 420, 440, 780, 819, 827, 843, 855, 856, 870, 876, 894, 1156]
  | 501 => [3, 21, 260, 275, 277, 284, 371, 420, 429, 440, 780, 827, 843, 856, 863, 870, 876, 881, 1156, 1161]
  | 502 => [3, 21, 260, 275, 277, 284, 371, 420, 440, 780, 819, 827, 843, 856, 863, 870, 876, 892, 1156, 1161]
  | 503 => [3, 21, 260, 275, 277, 285, 371, 420, 440, 780, 827, 836, 843, 856, 863, 870, 876, 879, 1139, 1156]
  | 505 => [3, 21, 260, 275, 277, 295, 371, 420, 439, 440, 780, 827, 836, 843, 856, 870, 876, 881, 1139, 1156]
  | 507 => [3, 21, 260, 275, 277, 295, 371, 420, 440, 780, 827, 836, 843, 855, 856, 870, 876, 883, 1139, 1156]
  | 509 => [3, 21, 260, 275, 277, 371, 420, 440, 780, 827, 836, 843, 856, 863, 870, 876, 881, 1139, 1156, 1161]
  | 511 => [3, 21, 260, 275, 277, 371, 440, 442, 827, 843, 856, 870, 1156]
  | 512 => [3, 21, 260, 276, 371, 425, 440, 751, 804, 843, 856, 862, 1142, 1153]
  | 513 => [3, 21, 260, 277, 371, 420, 440, 780, 827, 843, 856, 870, 1153, 1156]
  | _ => []
private def src141 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,244,782,853,1117],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,244,782,853,1117]]
private def recs141 : List LowerHistoryRecord := [⟨.left,141,0,(-1),false,204,1004⟩,⟨.left,141,1,(-1),false,203,148⟩]
private theorem check141 : recs141.all (recordCheck path141 src141 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path141_binding : lowerHistoryPathBinding path141 := by
  apply pathBinding_from_ids path141 src141 [] recs141 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues17.source141 rfl records141 rfl
  · intro r hr _
    simp only [recs141, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise204)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise203)
  · intro r hr _
    simp only [recs141, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [wids, path141] using WitnessLookup17.witness1004_projection
    · simpa only [wids, path141] using WitnessLookup17.witness148_projection
  · exact check141
  · exact BatchCoverage15.coverage_sound path141 recs141
      records141 SourceValues17.length141 BatchCoverageAll17.coverage141
private def src142 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,1078,403,609,1039,397,590,691,969,196],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,1078,403,609,1039,397,590,691,969,196]]
private def recs142 : List LowerHistoryRecord := [⟨.left,142,0,(-1),false,190,870⟩,⟨.left,142,1,(-1),false,189,118⟩]
private theorem check142 : recs142.all (recordCheck path142 src142 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path142_binding : lowerHistoryPathBinding path142 := by
  apply pathBinding_from_ids path142 src142 [] recs142 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues17.source142 rfl records142 rfl
  · intro r hr _
    simp only [recs142, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise190)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise189)
  · intro r hr _
    simp only [recs142, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [wids, path142] using WitnessLookup17.witness870_projection
    · simpa only [wids, path142] using WitnessLookup17.witness118_projection
  · exact check142
  · exact BatchCoverage15.coverage_sound path142 recs142
      records142 SourceValues17.length142 BatchCoverageAll17.coverage142
private def src143 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,1078,396,653,1073,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,1078,396,653,215,706,616,1082,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,220,869,396,653,1073,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,220,869,396,653,215,706,616,1082,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,1078,396,653,1073,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,1078,396,653,215,706,616,1082,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,220,869,396,653,1073,387,602,725,990,159],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,220,869,396,653,215,706,616,1082,387,602,725,990,159]]
private def recs143 : List LowerHistoryRecord := [⟨.left,143,0,(-1),false,178,900⟩,⟨.left,143,1,(-1),false,174,900⟩,⟨.left,143,2,(-1),false,176,900⟩,⟨.left,143,3,(-1),false,172,900⟩,⟨.left,143,4,(-1),false,177,124⟩,⟨.left,143,5,(-1),false,173,124⟩,⟨.left,143,6,(-1),false,175,124⟩,⟨.left,143,7,(-1),false,171,124⟩]
private theorem check143 : recs143.all (recordCheck path143 src143 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path143_binding : lowerHistoryPathBinding path143 := by
  apply pathBinding_from_ids path143 src143 [] recs143 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues17.source143 rfl records143 rfl
  · intro r hr _
    simp only [recs143, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise178)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise174)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise176)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise172)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise177)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise173)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise175)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise171)
  · intro r hr _
    simp only [recs143, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [wids, path143] using WitnessLookup17.witness900_projection
    · simpa only [wids, path143] using WitnessLookup17.witness900_projection
    · simpa only [wids, path143] using WitnessLookup17.witness900_projection
    · simpa only [wids, path143] using WitnessLookup17.witness900_projection
    · simpa only [wids, path143] using WitnessLookup17.witness124_projection
    · simpa only [wids, path143] using WitnessLookup17.witness124_projection
    · simpa only [wids, path143] using WitnessLookup17.witness124_projection
    · simpa only [wids, path143] using WitnessLookup17.witness124_projection
  · exact check143
  · exact BatchCoverage15.coverage_sound path143 recs143
      records143 SourceValues17.length143 BatchCoverageAll17.coverage143
private def src144 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,219,728,1105,394,657,771,1026,179],[371,843,260,440,3,856,21,282,837,1165,419,784,810,6,769,13,219,728,237,761,687,1114,394,657,771,1026,179],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,219,728,1105,394,657,771,1026,179],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,810,6,769,13,219,728,237,761,687,1114,394,657,771,1026,179]]
private def recs144 : List LowerHistoryRecord := [⟨.left,144,0,(-1),false,182,942⟩,⟨.left,144,1,(-1),false,180,942⟩,⟨.left,144,2,(-1),false,181,130⟩,⟨.left,144,3,(-1),false,179,130⟩]
private theorem check144 : recs144.all (recordCheck path144 src144 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path144_binding : lowerHistoryPathBinding path144 := by
  apply pathBinding_from_ids path144 src144 [] recs144 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues17.source144 rfl records144 rfl
  · intro r hr _
    simp only [recs144, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise182)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise180)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise181)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise179)
  · intro r hr _
    simp only [recs144, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [wids, path144] using WitnessLookup17.witness942_projection
    · simpa only [wids, path144] using WitnessLookup17.witness942_projection
    · simpa only [wids, path144] using WitnessLookup17.witness130_projection
    · simpa only [wids, path144] using WitnessLookup17.witness130_projection
  · exact check144
  · exact BatchCoverage15.coverage_sound path144 recs144
      records144 SourceValues17.length144 BatchCoverageAll17.coverage144
private def src145 : List (List Nat) := [[371,843,260,440,3,856,21,282,837,1165,419,784,270,831,1164,417,782,853,1117,244],[371,843,260,440,3,856,21,282,837,1165,419,784,270,831,286,846,805,1173,417,782,853,1117,244],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,270,831,1164,417,782,853,1117,244],[371,843,260,440,3,856,21,282,837,287,852,811,1181,419,784,270,831,286,846,805,1173,417,782,853,1117,244]]
private def recs145 : List LowerHistoryRecord := [⟨.left,145,0,(-1),false,434,1004⟩,⟨.left,145,1,(-1),false,432,65⟩,⟨.left,145,2,(-1),false,433,148⟩,⟨.left,145,3,(-1),false,431,148⟩]
private theorem check145 : recs145.all (recordCheck path145 src145 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path145_binding : lowerHistoryPathBinding path145 := by
  apply pathBinding_from_ids path145 src145 [] recs145 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues17.source145 rfl records145 rfl
  · intro r hr _
    simp only [recs145, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise434)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise432)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise433)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise431)
  · intro r hr _
    simp only [recs145, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [wids, path145] using WitnessLookup17.witness1004_projection
    · simpa only [wids, path145] using WitnessLookup17.witness65_projection
    · simpa only [wids, path145] using WitnessLookup17.witness148_projection
    · simpa only [wids, path145] using WitnessLookup17.witness148_projection
  · exact check145
  · exact BatchCoverage15.coverage_sound path145 recs145
      records145 SourceValues17.length145 BatchCoverageAll17.coverage145
end BatchIdSolution100
theorem _root_.solution : lowerHistoryBindingBatch 140 145 := by
  intro i hlo hhi p hp
  interval_cases i
  · have he := Option.some.inj (PathLookup17.path141_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution100.path141_binding
  · have he := Option.some.inj (PathLookup17.path142_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution100.path142_binding
  · have he := Option.some.inj (PathLookup17.path143_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution100.path143_binding
  · have he := Option.some.inj (PathLookup17.path144_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution100.path144_binding
  · have he := Option.some.inj (PathLookup17.path145_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution100.path145_binding
end M7Binding100Sep15
#print axioms solution
