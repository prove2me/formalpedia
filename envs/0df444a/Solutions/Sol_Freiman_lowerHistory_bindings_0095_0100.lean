-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0095_0100
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T10:13:01.605542+00:00
-- url     : https://prove2.me/submissions/d17a681a-c682-4af9-ab35-5d59355b23c2

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
namespace M7Binding50Sep15
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
structure SourceOps where
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
namespace BindingNumeric16
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
private theorem norm2 : lowerHistoryNormalization ([2,1],[3,1]) false false = ⟨false,false,⟨⟨(13/10),0,0,(9/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm9 : lowerHistoryNormalization ([2,1,3,1],[3,1]) true true = ⟨true,true,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm20 : lowerHistoryNormalization ([2,1,2,1],[3,1]) true true = ⟨true,true,⟨⟨(15/134),0,0,(23/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm33 : lowerHistoryNormalization ([2,1,3],[3,1]) true true = ⟨true,true,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm34 : lowerHistoryNormalization ([2,1,2],[3,1]) true true = ⟨true,true,⟨⟨(41/185),0,0,(32/1295)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm35 : lowerHistoryNormalization ([2,1,1],[3,1]) true false = ⟨true,false,⟨⟨(43/94),0,0,(37/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm36 : lowerHistoryNormalization ([2,1,1,1],[3,1]) true true = ⟨true,true,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm48 : lowerHistoryNormalization ([2],[3]) true false = ⟨true,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm49 : lowerHistoryNormalization ([2],[3,1]) false false = ⟨false,false,⟨⟨3,0,0,(2/5)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm52 : lowerHistoryNormalization ([2],[3,1]) true false = ⟨true,false,⟨⟨3,0,0,(2/5)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm53 : lowerHistoryNormalization ([2,1],[3,1]) true true = ⟨true,true,⟨⟨(13/10),0,0,(9/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm54 : lowerHistoryNormalization ([2,3],[3,1]) true false = ⟨true,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey5 : lowerHistoryPull (lowerHistoryH7) ([2,1,1,1],[3,1]) true = ⟨false,false,⟨⟨(1140100/839201),(-323050/839201),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey6 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1],[3,1]) true = ⟨false,true,⟨⟨(387429/2003254),(677093/6009762),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey7 : lowerHistoryPull (lowerHistoryHN) ([2,1,1,1],[3,1]) true = ⟨true,false,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey8 : lowerHistoryPull (lowerHistoryH7) ([2,1],[3,1]) true = ⟨false,false,⟨⟨(3450950/367939),(-2939050/1103817),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey9 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1],[3,1]) true = ⟨false,true,⟨⟨(56083/42081),(32672/42081),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey10 : lowerHistoryPull (lowerHistoryHN) ([2,1],[3,1]) true = ⟨true,false,⟨⟨(13/10),0,0,(9/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey15 : lowerHistoryPull (lowerHistoryH2) ([2,1,3],[3,1]) true = ⟨false,true,⟨⟨(329014964650/1370729503247),(2276619750/1370729503247),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(12510/34801),(1/34801),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey16 : lowerHistoryPull (lowerHistoryH7) ([2,1,3,1],[3,1]) true = ⟨false,false,⟨⟨(1595970350/4021318543),(-455592800/4021318543),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey17 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,3,1],[3,1]) true = ⟨false,true,⟨⟨(1322907/23585446),(2312189/70756338),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey18 : lowerHistoryPull (lowerHistoryHN) ([2,1,3,1],[3,1]) true = ⟨true,false,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey45 : lowerHistoryPull (lowerHistoryH2) ([2,1,2],[3,1]) true = ⟨false,true,⟨⟨(807277100/1984682089),(189129600/73433237293),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey46 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,2],[3,1]) true = ⟨false,false,⟨⟨(542698100500/1049991995709),(375206500/33870709539),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey47 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,1,2],[3,1]) true = ⟨false,false,⟨⟨(5016197/29731444),(7213297/44597166),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(4183/11279),(-1/33837),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey48 : lowerHistoryPull (lowerHistoryH23) ([2,1,2],[3,1]) true = ⟨false,true,⟨⟨(49773906500/85582105817),(-2106222500/85582105817),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey49 : lowerHistoryPull (lowerHistoryH7) ([2,1,2,1],[3,1]) true = ⟨false,false,⟨⟨(1890656950/2826713021),(-538238350/2826713021),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey50 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,1],[3,1]) true = ⟨false,true,⟨⟨(785697/8289481),(1373204/24868443),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey51 : lowerHistoryPull (lowerHistoryHN) ([2,1,2,1],[3,1]) true = ⟨true,false,⟨⟨(15/134),0,0,(23/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey82 : lowerHistoryPull (lowerHistoryH7) ([2,1],[3,1]) false = ⟨true,false,⟨⟨(8164501/16382860),(11119731/81914300),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey83 : lowerHistoryPull (lowerHistoryH9) ([2,1],[3,1]) false = ⟨false,false,⟨⟨(6639/169),(-3704/169),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey84 : lowerHistoryPull (lowerHistoryH2) ([2,1,1],[3,1]) true = ⟨false,true,⟨⟨(8603517050/10310778049),(45310050/10310778049),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey85 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) true = ⟨false,false,⟨⟨(124480872500/110611274499),(1112783000/110611274499),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey86 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,1,1],[3,1]) true = ⟨false,false,⟨⟨(1196893/3209954),(6769901/19259724),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(1929/4946),(-1/14838),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey87 : lowerHistoryPull (lowerHistoryH23) ([2,1,1],[3,1]) true = ⟨false,true,⟨⟨(23558673500/19023740021),(-1556463500/19023740021),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey117 : lowerHistoryPull (lowerHistoryH7) ([2,3],[3,1]) true = ⟨false,false,⟨⟨(180467950/78144583),(-151370050/234433749),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey118 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,3],[3,1]) true = ⟨false,true,⟨⟨(228931/687489),(44448/229163),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey119 : lowerHistoryPull (lowerHistoryHN) ([2,3],[3,1]) true = ⟨true,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey123 : lowerHistoryPull (lowerHistoryH2) ([2],[3,1]) true = ⟨false,true,⟨⟨(9176371900/1599461123),(157090000/4798383369),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey124 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2],[3,1]) true = ⟨false,false,⟨⟨(399471500/52948737),(531972500/4924232541),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey125 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2],[3,1]) true = ⟨false,false,⟨⟨(263566/106079),(1000743/424316),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey126 : lowerHistoryPull (lowerHistoryH23) ([2],[3,1]) true = ⟨false,true,⟨⟨(10406959500/1242039643),(-583115500/1242039643),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey127 : lowerHistoryPull (lowerHistoryH7) ([2],[3]) false = ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey128 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = ⟨true,true,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pull51 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) true = ⟨true,false,⟨⟨(807277100/1984682089),(189129600/73433237293),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey45]
  rfl
private theorem pull92 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH7) ([2,1],[3,1]) false = ⟨false,true,⟨⟨(8164501/16382860),(11119731/81914300),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey82]
  rfl
private theorem pull96 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) true = ⟨true,false,⟨⟨(8603517050/10310778049),(45310050/10310778049),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey84]
  rfl
private theorem pull140 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2],[3,1]) true = ⟨true,false,⟨⟨(9176371900/1599461123),(157090000/4798383369),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey123]
  rfl
end BindingNumeric16
set_option Elab.async false

open Freiman
namespace BindingSourceBranches16
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem branchesG1 :
    (lowerHistoryNecessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[1]),true)⟩ ([2,1,3],[3,1]) = some [⟨false,false,⟨⟨(1586290/10727197),(3840344/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,3,1],[3,1]) = some [⟨false,false,⟨⟨(21401836/181871027),(16030791/181871027),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,1,3],[3,1]) = some [⟨true,false,⟨⟨(-8845164/47149609),(6653521/47149609),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,3,3],[3,1]) = some [⟨false,false,⟨⟨(79147520/5472314497),(174559212/5472314497),0,0⟩,⟨(50716/140269),(1/140269),0,0⟩,⟨(1086/3001),(-1/3001),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,3,2],[3,1]) = some [⟨false,false,⟨⟨(136936/5095883),(337299/5095883),0,0⟩,⟨(1991/5521),(1/5521),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,3,1],[3,1]) = some [⟨false,false,⟨⟨(21401836/181871027),(16030791/181871027),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,3,1],[3,1]) = some [⟨true,false,⟨⟨(-21593634/271232629),(16126691/271232629),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,3,1,2],[3,1]) = some [⟨false,false,⟨⟨(3334901/319441187),(9556540/319441187),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
  decide +kernel
private theorem branchesG2 :
    (lowerHistoryNecessary ⟨⟨([1,2,1,3,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,3,1,2,1],[3,1]) = some [⟨false,false,⟨⟨(5054340/840078733),(27711379/2520236199),0,0⟩,⟨(3679/10259),(1/30777),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,3,1,1],[3,1]) = some [⟨false,false,⟨⟨(2408143/87283079),(5086662/87283079),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,3,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(6926918/613103699),(13570693/613103699),0,0⟩,⟨(5604/15601),(1/15601),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[1]),true)⟩ ([2,1,2],[3,1]) = some [⟨false,false,⟨⟨(7617/30251),(63275/90753),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,2,1],[3,1]) = some [⟨false,false,⟨⟨(214600/1533493),(1183231/4600479),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [⟨true,false,⟨⟨(-5111577/15657181),(3840568/15657181),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,2,3],[3,1]) = some [⟨false,false,⟨⟨(42724568/1681253509),(96584076/1681253509),0,0⟩,⟨(28970/78049),(1/78049),0,0⟩,⟨(616/1657),(-1/1657),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,2,2],[3,1]) = some [⟨false,false,⟨⟨(972280/21096959),(2470191/21096959),0,0⟩,⟨(1161/3142),(1/3142),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
  decide +kernel
private theorem branchesG4 :
    (lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([],[1]),false)⟩ ([2,1],[3,1]) = some [⟨true,false,⟨⟨(-605239/322621),(452861/322621),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,3],[3,1]) = some [⟨false,false,⟨⟨(1586290/10727197),(3840344/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,2],[3,1]) = some [⟨false,false,⟨⟨(7617/30251),(63275/90753),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [⟨false,false,⟨⟨(34974/50713),(213073/152139),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(188333/700271),(1121999/2100813),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,1,3],[3,1]) = some [⟨false,false,⟨⟨(17414528/312797329),(41514444/312797329),0,0⟩,⟨(13260/33937),(1/33937),0,0⟩,⟨(278/709),(-1/709),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,1,3],[3]) = some [⟨false,false,⟨⟨(619410/10727197),(1569896/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,3],[3,1]) = some [⟨true,false,⟨⟨(-8845164/47149609),(6653521/47149609),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩]) := by
  decide +kernel
private theorem branchesG6 :
    (lowerHistoryNecessary ⟨⟨([1,2,1,1,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1,3,1],[3,1]) = some [⟨false,false,⟨⟨(298695031/17701635601),(223705319/17701635601),0,0⟩,⟨(33275/87889),(-1/87889),0,0⟩,⟨(5866/15493),(1/15493),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,1,1,2],[3,1]) = some [⟨false,false,⟨⟨(94960/2585869),(259781/2585869),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1,2,1],[3,1]) = some [⟨false,false,⟨⟨(134877/6694259),(745220/20082777),0,0⟩,⟨(1157/3047),(1/9141),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(731824/7179887),(1465575/7179887),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(1923725/49263539),(3840076/49263539),0,0⟩,⟨(1700/4453),(1/4453),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [⟨false,false,⟨⟨(34974/50713),(213073/152139),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([2],[3]) = some [⟨false,false,⟨⟨(10485/6253),(24757/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[3,1]) = some [⟨true,false,⟨⟨(-5134/1081),(3851/1081),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩]) := by
  decide +kernel
private theorem branchesG7 :
    (lowerHistoryNecessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,3],[3,1]) = some [⟨false,false,⟨⟨(911720/2447159),(6369548/7341477),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,2],[3,1]) = some [⟨false,false,⟨⟨(21019/31993),(166288/95979),0,0⟩,⟨(89/214),(1/214),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1],[3,1]) = some [⟨false,false,⟨⟨(43019/22607),(82570/22607),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1],[3,1]) = some [⟨true,false,⟨⟨(-605239/322621),(452861/322621),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2],[3,1]) = some [⟨false,false,⟨⟨(26765/6253),(60573/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1],[3,1]) = some [⟨false,false,⟨⟨(43019/22607),(82570/22607),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([2,2,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[1]),true)⟩ ([2,3],[3,1]) = some [⟨false,false,⟨⟨(911720/2447159),(6369548/7341477),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
  decide +kernel
end BindingSourceBranches16

open Freiman
namespace BindingSourceSupport16
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem relaxed1 : lowerHistoryRelaxedGoodness ⟨([1],[3,1]),(false,false)⟩ = some [⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩] := by
  decide +kernel
private theorem relaxed2 : lowerHistoryRelaxedGoodness ⟨([2],[3,1]),(false,false)⟩ = some [⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩] := by
  decide +kernel
private def fingerprint (b : CertBound) : Bool × Bool × Rat × Rat × Rat × Rat := (b.lower,b.strict,b.threshold.c.a,b.threshold.c.b,b.threshold.x0.a,b.threshold.x1.a)
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
end BindingSourceSupport16

open Freiman
open RootOps19
set_option linter.all false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace BindingOps16_96
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b1 : CertBound) (b2 : CertBound) (b3 : CertBound) (b260 : CertBound) (b262 : CertBound) (b293 : CertBound) (b371 : CertBound) (b423 : CertBound) (b426 : CertBound) (b440 : CertBound) (b736 : CertBound) (b752 : CertBound) (b809 : CertBound) (b843 : CertBound) (b851 : CertBound) (b857 : CertBound) (b867 : CertBound) (b1071 : CertBound) (b1132 : CertBound) (b1152 : CertBound)
private def path : LowerHistoryPath := ⟨.left,96,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([2],[3]) = some [b857])
    (hb1 : ops.necessary ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[3,1]) = some [b1])
    (hb2 : ops.necessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1],[3,1]) = some [b2])
    (hb3 : ops.necessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,3],[3,1]) = some [b752])
    (hb4 : ops.necessary ⟨⟨([1,2,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,3,1],[3,1]) = some [b736])
    (hn0 : ops.normalization ([2],[3]) true false = b293)
    (hn1 : ops.normalization ([2],[3,1]) false false = b867)
    (hn2 : ops.normalization ([2,1],[3,1]) false false = b851)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,1],[3,1]) false = b1152)
    (hn4 : ops.normalization ([2,1,3],[3,1]) true true = b426)
    (hn5 : ops.pull (lowerHistoryH2) ([2,1,3],[3,1]) true = b1132)
    (hn6 : ops.normalization ([2,1,3,1],[3,1]) true true = b423)
    (hn7 : ops.pull (lowerHistoryH7) ([2,1,3,1],[3,1]) true = b809)
    (hn8 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,3,1],[3,1]) true = b1071)
    (hn9 : ops.pull (lowerHistoryHN) ([2,1,3,1],[3,1]) true = b262)
    (herase0 : [b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b426,b752,b1132,b423,b736,b809,b1071,b262].eraseDups = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b426,b752,b1132,b423,b736,b809,b1071,b262]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b426,b752,b1132,b423,b736,b809,b1071,b262]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH7]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps16_96
namespace BindingOps16_97
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b1 : CertBound) (b2 : CertBound) (b3 : CertBound) (b236 : CertBound) (b260 : CertBound) (b266 : CertBound) (b274 : CertBound) (b293 : CertBound) (b371 : CertBound) (b414 : CertBound) (b418 : CertBound) (b440 : CertBound) (b747 : CertBound) (b763 : CertBound) (b779 : CertBound) (b813 : CertBound) (b829 : CertBound) (b843 : CertBound) (b851 : CertBound) (b857 : CertBound) (b867 : CertBound) (b878 : CertBound) (b1093 : CertBound) (b1145 : CertBound) (b1152 : CertBound) (b1155 : CertBound)
private def path : LowerHistoryPath := ⟨.left,97,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([2],[3]) = some [b857])
    (hb1 : ops.necessary ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[3,1]) = some [b1])
    (hb2 : ops.necessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1],[3,1]) = some [b2])
    (hb3 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,2],[3,1]) = some [b779])
    (hb4 : ops.necessary ⟨⟨([1,2,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,2,1],[3,1]) = some [b747])
    (hn0 : ops.normalization ([2],[3]) true false = b293)
    (hn1 : ops.normalization ([2],[3,1]) false false = b867)
    (hn2 : ops.normalization ([2,1],[3,1]) false false = b851)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,1],[3,1]) false = b1152)
    (hn4 : ops.pull (lowerHistoryH7) ([2,1],[3,1]) false = b274)
    (hn5 : ops.pull (lowerHistoryH9) ([2,1],[3,1]) false = b878)
    (hn6 : ops.normalization ([2,1,2],[3,1]) true true = b418)
    (hn7 : ops.pull (lowerHistoryH2) ([2,1,2],[3,1]) true = b1145)
    (hn8 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) true = b266)
    (hn9 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,2],[3,1]) true = b813)
    (hn10 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1,2],[3,1]) true = b763)
    (hn11 : ops.pull (lowerHistoryH23) ([2,1,2],[3,1]) true = b1155)
    (hn12 : ops.normalization ([2,1,2,1],[3,1]) true true = b414)
    (hn13 : ops.pull (lowerHistoryH7) ([2,1,2,1],[3,1]) true = b829)
    (hn14 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,1],[3,1]) true = b1093)
    (hn15 : ops.pull (lowerHistoryHN) ([2,1,2,1],[3,1]) true = b236)
    (herase0 : [b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b1145,b414,b747,b829,b1093,b236].eraseDups = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236].eraseDups = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236]
] : List (List CertBound))[1])
    (herase2 : [b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b1145,b414,b747,b829,b1093,b236].eraseDups = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236]
] : List (List CertBound))[2])
    (herase3 : [b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236].eraseDups = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236]
] : List (List CertBound))[3])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b1152,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b1145,b414,b747,b829,b1093,b236],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b274,b878,b418,b779,b266,b813,b763,b1155,b414,b747,b829,b1093,b236]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1, herase2, herase3]
  rfl
end BindingOps16_97
namespace BindingOps16_98
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b1 : CertBound) (b2 : CertBound) (b3 : CertBound) (b244 : CertBound) (b260 : CertBound) (b270 : CertBound) (b286 : CertBound) (b293 : CertBound) (b371 : CertBound) (b417 : CertBound) (b440 : CertBound) (b782 : CertBound) (b805 : CertBound) (b831 : CertBound) (b843 : CertBound) (b846 : CertBound) (b851 : CertBound) (b853 : CertBound) (b857 : CertBound) (b867 : CertBound) (b1117 : CertBound) (b1164 : CertBound) (b1173 : CertBound)
private def path : LowerHistoryPath := ⟨.left,98,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([2],[3]) = some [b857])
    (hb1 : ops.necessary ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[3,1]) = some [b1])
    (hb2 : ops.necessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1],[3,1]) = some [b2])
    (hb3 : ops.necessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [b831])
    (hb4 : ops.necessary ⟨⟨([1,2,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,1,1],[3,1]) = some [b782])
    (hn0 : ops.normalization ([2],[3]) true false = b293)
    (hn1 : ops.normalization ([2],[3,1]) false false = b867)
    (hn2 : ops.normalization ([2,1],[3,1]) false false = b851)
    (hn3 : ops.normalization ([2,1,1],[3,1]) true false = b270)
    (hn4 : ops.pull (lowerHistoryH2) ([2,1,1],[3,1]) true = b1164)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,1],[3,1]) true = b286)
    (hn6 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,1],[3,1]) true = b846)
    (hn7 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1,1],[3,1]) true = b805)
    (hn8 : ops.pull (lowerHistoryH23) ([2,1,1],[3,1]) true = b1173)
    (hn9 : ops.normalization ([2,1,1,1],[3,1]) true true = b417)
    (hn10 : ops.pull (lowerHistoryH7) ([2,1,1,1],[3,1]) true = b853)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,1,1],[3,1]) true = b1117)
    (hn12 : ops.pull (lowerHistoryHN) ([2,1,1,1],[3,1]) true = b244)
    (herase0 : [b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b270,b831,b1164,b417,b782,b853,b1117,b244].eraseDups = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244].eraseDups = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244]
] : List (List CertBound))[1])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b270,b831,b1164,b417,b782,b853,b1117,b244],
[b371,b843,b260,b440,b3,b293,b857,b867,b1,b851,b2,b270,b831,b286,b846,b805,b1173,b417,b782,b853,b1117,b244]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1]
  rfl
end BindingOps16_98
namespace BindingOps16_99
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b260 : CertBound) (b292 : CertBound) (b293 : CertBound) (b297 : CertBound) (b298 : CertBound) (b371 : CertBound) (b438 : CertBound) (b440 : CertBound) (b843 : CertBound) (b857 : CertBound) (b860 : CertBound) (b864 : CertBound) (b872 : CertBound) (b874 : CertBound) (b875 : CertBound) (b1180 : CertBound) (b1187 : CertBound) (b1188 : CertBound)
private def path : LowerHistoryPath := ⟨.left,99,[1],([2],[3]),true,[(([1],[]),false),(([],[1]),false)],([1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([2],[3]) = some [b857])
    (hb1 : ops.necessary ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2],[3,1]) = some [b872])
    (hb2 : ops.necessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1],[3,1]) = some [b860])
    (hn0 : ops.normalization ([2],[3]) true false = b293)
    (hn1 : ops.normalization ([2],[3,1]) true false = b297)
    (hn2 : ops.pull (lowerHistoryH2) ([2],[3,1]) true = b1187)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2],[3,1]) true = b298)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2],[3,1]) true = b874)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2],[3,1]) true = b864)
    (hn6 : ops.pull (lowerHistoryH23) ([2],[3,1]) true = b1188)
    (hn7 : ops.normalization ([2,1],[3,1]) true true = b438)
    (hn8 : ops.pull (lowerHistoryH7) ([2,1],[3,1]) true = b875)
    (hn9 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1],[3,1]) true = b1180)
    (hn10 : ops.pull (lowerHistoryHN) ([2,1],[3,1]) true = b292)
    (herase0 : [b371,b843,b260,b440,b3,b293,b857,b297,b872,b1187,b438,b860,b875,b1180,b292].eraseDups = ([
[b371,b843,b260,b440,b3,b293,b857,b297,b872,b1187,b438,b860,b875,b1180,b292],
[b371,b843,b260,b440,b3,b293,b857,b297,b872,b298,b874,b864,b1188,b438,b860,b875,b1180,b292]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b293,b857,b297,b872,b298,b874,b864,b1188,b438,b860,b875,b1180,b292].eraseDups = ([
[b371,b843,b260,b440,b3,b293,b857,b297,b872,b1187,b438,b860,b875,b1180,b292],
[b371,b843,b260,b440,b3,b293,b857,b297,b872,b298,b874,b864,b1188,b438,b860,b875,b1180,b292]
] : List (List CertBound))[1])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b293,b857,b297,b872,b1187,b438,b860,b875,b1180,b292],
[b371,b843,b260,b440,b3,b293,b857,b297,b872,b298,b874,b864,b1188,b438,b860,b875,b1180,b292]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,true,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1]
  rfl
end BindingOps16_99
namespace BindingOps16_100
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b21 : CertBound) (b260 : CertBound) (b275 : CertBound) (b276 : CertBound) (b371 : CertBound) (b440 : CertBound) (b442 : CertBound) (b804 : CertBound) (b843 : CertBound) (b856 : CertBound) (b862 : CertBound) (b1142 : CertBound)
private def path : LowerHistoryPath := ⟨.left,100,[2],([2],[3]),false,[(([3],[1]),true)],([2,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([2],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([2,2,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[1]),true)⟩ ([2,3],[3,1]) = some [b804])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,3],[3,1]) true false = b276)
    (hn4 : ops.pull (lowerHistoryH7) ([2,3],[3,1]) true = b862)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,3],[3,1]) true = b1142)
    (hn6 : ops.pull (lowerHistoryHN) ([2,3],[3,1]) true = b276)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b276,b804,b862,b1142,b276].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b276,b804,b862,b1142]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b276,b804,b862,b1142]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([2,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([3],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hdone, hchoice0, hdone0, hforced0, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps16_100

open Freiman

private def sourceBound1 : CertBound := ⟨true,false,⟨⟨(-5134/1081),(3851/1081),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def sourceBound2 : CertBound := ⟨true,false,⟨⟨(-605239/322621),(452861/322621),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def sourceBound3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩

private def sourceBound21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def sourceBound236 : CertBound := ⟨true,false,⟨⟨(15/134),0,0,(23/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound244 : CertBound := ⟨true,false,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound260 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private def sourceBound262 : CertBound := ⟨true,false,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound266 : CertBound := ⟨true,false,⟨⟨(807277100/1984682089),(189129600/73433237293),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound270 : CertBound := ⟨true,false,⟨⟨(43/94),0,0,(37/658)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound274 : CertBound := ⟨true,false,⟨⟨(8164501/16382860),(11119731/81914300),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound275 : CertBound := ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def sourceBound276 : CertBound := ⟨true,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound286 : CertBound := ⟨true,false,⟨⟨(8603517050/10310778049),(45310050/10310778049),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound292 : CertBound := ⟨true,false,⟨⟨(13/10),0,0,(9/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound293 : CertBound := ⟨true,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def sourceBound297 : CertBound := ⟨true,false,⟨⟨3,0,0,(2/5)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound298 : CertBound := ⟨true,false,⟨⟨(9176371900/1599461123),(157090000/4798383369),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound371 : CertBound := ⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

private def sourceBound414 : CertBound := ⟨true,true,⟨⟨(15/134),0,0,(23/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound417 : CertBound := ⟨true,true,⟨⟨(1101/6157),0,0,(128/6157)⟩,⟨(31/94),0,0,(1/94)⟩,⟨(105/262),0,0,(-1/262)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound418 : CertBound := ⟨true,true,⟨⟨(41/185),0,0,(32/1295)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound423 : CertBound := ⟨true,true,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound426 : CertBound := ⟨true,true,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound438 : CertBound := ⟨true,true,⟨⟨(13/10),0,0,(9/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private def sourceBound442 : CertBound := ⟨true,true,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def sourceBound736 : CertBound := ⟨false,false,⟨⟨(21401836/181871027),(16030791/181871027),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound747 : CertBound := ⟨false,false,⟨⟨(214600/1533493),(1183231/4600479),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound752 : CertBound := ⟨false,false,⟨⟨(1586290/10727197),(3840344/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound763 : CertBound := ⟨false,false,⟨⟨(5016197/29731444),(7213297/44597166),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(4183/11279),(-1/33837),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound779 : CertBound := ⟨false,false,⟨⟨(7617/30251),(63275/90753),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound782 : CertBound := ⟨false,false,⟨⟨(188333/700271),(1121999/2100813),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound804 : CertBound := ⟨false,false,⟨⟨(911720/2447159),(6369548/7341477),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound805 : CertBound := ⟨false,false,⟨⟨(1196893/3209954),(6769901/19259724),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(1929/4946),(-1/14838),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound809 : CertBound := ⟨false,false,⟨⟨(1595970350/4021318543),(-455592800/4021318543),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound813 : CertBound := ⟨false,false,⟨⟨(542698100500/1049991995709),(375206500/33870709539),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private def sourceBound829 : CertBound := ⟨false,false,⟨⟨(1890656950/2826713021),(-538238350/2826713021),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound831 : CertBound := ⟨false,false,⟨⟨(34974/50713),(213073/152139),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound843 : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩

private def sourceBound846 : CertBound := ⟨false,false,⟨⟨(124480872500/110611274499),(1112783000/110611274499),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private def sourceBound851 : CertBound := ⟨false,false,⟨⟨(13/10),0,0,(9/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound853 : CertBound := ⟨false,false,⟨⟨(1140100/839201),(-323050/839201),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound856 : CertBound := ⟨false,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def sourceBound857 : CertBound := ⟨false,false,⟨⟨(10485/6253),(24757/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def sourceBound860 : CertBound := ⟨false,false,⟨⟨(43019/22607),(82570/22607),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound862 : CertBound := ⟨false,false,⟨⟨(180467950/78144583),(-151370050/234433749),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound864 : CertBound := ⟨false,false,⟨⟨(263566/106079),(1000743/424316),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound867 : CertBound := ⟨false,false,⟨⟨3,0,0,(2/5)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound872 : CertBound := ⟨false,false,⟨⟨(26765/6253),(60573/6253),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound874 : CertBound := ⟨false,false,⟨⟨(399471500/52948737),(531972500/4924232541),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private def sourceBound875 : CertBound := ⟨false,false,⟨⟨(3450950/367939),(-2939050/1103817),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound878 : CertBound := ⟨false,false,⟨⟨(6639/169),(-3704/169),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1071 : CertBound := ⟨false,true,⟨⟨(1322907/23585446),(2312189/70756338),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1093 : CertBound := ⟨false,true,⟨⟨(785697/8289481),(1373204/24868443),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1117 : CertBound := ⟨false,true,⟨⟨(387429/2003254),(677093/6009762),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1132 : CertBound := ⟨false,true,⟨⟨(329014964650/1370729503247),(2276619750/1370729503247),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(12510/34801),(1/34801),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1142 : CertBound := ⟨false,true,⟨⟨(228931/687489),(44448/229163),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1145 : CertBound := ⟨false,true,⟨⟨(807277100/1984682089),(189129600/73433237293),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1152 : CertBound := ⟨false,true,⟨⟨(8164501/16382860),(11119731/81914300),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1155 : CertBound := ⟨false,true,⟨⟨(49773906500/85582105817),(-2106222500/85582105817),0,0⟩,⟨(7480/20353),(1/20353),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1164 : CertBound := ⟨false,true,⟨⟨(8603517050/10310778049),(45310050/10310778049),0,0⟩,⟨(1413/3718),(-1/3718),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1173 : CertBound := ⟨false,true,⟨⟨(23558673500/19023740021),(-1556463500/19023740021),0,0⟩,⟨(3734/9757),(1/9757),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1180 : CertBound := ⟨false,true,⟨⟨(56083/42081),(32672/42081),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1187 : CertBound := ⟨false,true,⟨⟨(9176371900/1599461123),(157090000/4798383369),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1188 : CertBound := ⟨false,true,⟨⟨(10406959500/1242039643),(-583115500/1242039643),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

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
namespace SourceMemo16_96
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,96,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound1152,sourceBound426,sourceBound752,sourceBound1132,sourceBound423,sourceBound736,sourceBound809,sourceBound1071,sourceBound262]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound1152,sourceBound426,sourceBound752,sourceBound1132,sourceBound423,sourceBound736,sourceBound809,sourceBound1071,sourceBound262].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_96.source_structural (ops := RootOps19.actualOps) (b1 := sourceBound1) (b2 := sourceBound2) (b3 := sourceBound3) (b260 := sourceBound260) (b262 := sourceBound262) (b293 := sourceBound293) (b371 := sourceBound371) (b423 := sourceBound423) (b426 := sourceBound426) (b440 := sourceBound440) (b736 := sourceBound736) (b752 := sourceBound752) (b809 := sourceBound809) (b843 := sourceBound843) (b851 := sourceBound851) (b857 := sourceBound857) (b867 := sourceBound867) (b1071 := sourceBound1071) (b1132 := sourceBound1132) (b1152 := sourceBound1152)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG6.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG6.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG7.2.2.2.1) (BindingSourceBranches16.branchesG4.2.1) (BindingSourceBranches16.branchesG1.2.1) BindingNumeric16.norm48 BindingNumeric16.norm49 BindingNumeric16.norm2 BindingNumeric16.pull92 BindingNumeric16.norm33 BindingNumeric16.pullKey15 BindingNumeric16.norm9 BindingNumeric16.pullKey16 BindingNumeric16.pullKey17 BindingNumeric16.pullKey18 eraseActual0)
end SourceMemo16_96

open Freiman
open Freiman
namespace SourceMemo16_97
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,97,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound1152,sourceBound418,sourceBound779,sourceBound1145,sourceBound414,sourceBound747,sourceBound829,sourceBound1093,sourceBound236],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound1152,sourceBound418,sourceBound779,sourceBound266,sourceBound813,sourceBound763,sourceBound1155,sourceBound414,sourceBound747,sourceBound829,sourceBound1093,sourceBound236],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound274,sourceBound878,sourceBound418,sourceBound779,sourceBound1145,sourceBound414,sourceBound747,sourceBound829,sourceBound1093,sourceBound236],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound274,sourceBound878,sourceBound418,sourceBound779,sourceBound266,sourceBound813,sourceBound763,sourceBound1155,sourceBound414,sourceBound747,sourceBound829,sourceBound1093,sourceBound236]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound1152,sourceBound418,sourceBound779,sourceBound1145,sourceBound414,sourceBound747,sourceBound829,sourceBound1093,sourceBound236].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound1152,sourceBound418,sourceBound779,sourceBound266,sourceBound813,sourceBound763,sourceBound1155,sourceBound414,sourceBound747,sourceBound829,sourceBound1093,sourceBound236].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem erase2 : expected[2].eraseDups = expected[2] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[2] (by simp [expected])))
private theorem eraseActual2 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound274,sourceBound878,sourceBound418,sourceBound779,sourceBound1145,sourceBound414,sourceBound747,sourceBound829,sourceBound1093,sourceBound236].eraseDups = expected[2] := by
  simpa [expected] using erase2
private theorem erase3 : expected[3].eraseDups = expected[3] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[3] (by simp [expected])))
private theorem eraseActual3 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound274,sourceBound878,sourceBound418,sourceBound779,sourceBound266,sourceBound813,sourceBound763,sourceBound1155,sourceBound414,sourceBound747,sourceBound829,sourceBound1093,sourceBound236].eraseDups = expected[3] := by
  simpa [expected] using erase3
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_97.source_structural (ops := RootOps19.actualOps) (b1 := sourceBound1) (b2 := sourceBound2) (b3 := sourceBound3) (b236 := sourceBound236) (b260 := sourceBound260) (b266 := sourceBound266) (b274 := sourceBound274) (b293 := sourceBound293) (b371 := sourceBound371) (b414 := sourceBound414) (b418 := sourceBound418) (b440 := sourceBound440) (b747 := sourceBound747) (b763 := sourceBound763) (b779 := sourceBound779) (b813 := sourceBound813) (b829 := sourceBound829) (b843 := sourceBound843) (b851 := sourceBound851) (b857 := sourceBound857) (b867 := sourceBound867) (b878 := sourceBound878) (b1093 := sourceBound1093) (b1145 := sourceBound1145) (b1152 := sourceBound1152) (b1155 := sourceBound1155)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG6.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG6.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG7.2.2.2.1) (BindingSourceBranches16.branchesG4.2.2.1) (BindingSourceBranches16.branchesG2.2.2.2.2.1) BindingNumeric16.norm48 BindingNumeric16.norm49 BindingNumeric16.norm2 BindingNumeric16.pull92 BindingNumeric16.pullKey82 BindingNumeric16.pullKey83 BindingNumeric16.norm34 BindingNumeric16.pullKey45 BindingNumeric16.pull51 BindingNumeric16.pullKey46 BindingNumeric16.pullKey47 BindingNumeric16.pullKey48 BindingNumeric16.norm20 BindingNumeric16.pullKey49 BindingNumeric16.pullKey50 BindingNumeric16.pullKey51 eraseActual0 eraseActual1 eraseActual2 eraseActual3)
end SourceMemo16_97

open Freiman
open Freiman
namespace SourceMemo16_98
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,98,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound270,sourceBound831,sourceBound1164,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound270,sourceBound831,sourceBound286,sourceBound846,sourceBound805,sourceBound1173,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound270,sourceBound831,sourceBound1164,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound867,sourceBound1,sourceBound851,sourceBound2,sourceBound270,sourceBound831,sourceBound286,sourceBound846,sourceBound805,sourceBound1173,sourceBound417,sourceBound782,sourceBound853,sourceBound1117,sourceBound244].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_98.source_structural (ops := RootOps19.actualOps) (b1 := sourceBound1) (b2 := sourceBound2) (b3 := sourceBound3) (b244 := sourceBound244) (b260 := sourceBound260) (b270 := sourceBound270) (b286 := sourceBound286) (b293 := sourceBound293) (b371 := sourceBound371) (b417 := sourceBound417) (b440 := sourceBound440) (b782 := sourceBound782) (b805 := sourceBound805) (b831 := sourceBound831) (b843 := sourceBound843) (b846 := sourceBound846) (b851 := sourceBound851) (b853 := sourceBound853) (b857 := sourceBound857) (b867 := sourceBound867) (b1117 := sourceBound1117) (b1164 := sourceBound1164) (b1173 := sourceBound1173)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG6.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG6.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG7.2.2.2.1) (BindingSourceBranches16.branchesG4.2.2.2.1) (BindingSourceBranches16.branchesG4.2.2.2.2.1) BindingNumeric16.norm48 BindingNumeric16.norm49 BindingNumeric16.norm2 BindingNumeric16.norm35 BindingNumeric16.pullKey84 BindingNumeric16.pull96 BindingNumeric16.pullKey85 BindingNumeric16.pullKey86 BindingNumeric16.pullKey87 BindingNumeric16.norm36 BindingNumeric16.pullKey5 BindingNumeric16.pullKey6 BindingNumeric16.pullKey7 eraseActual0 eraseActual1)
end SourceMemo16_98

open Freiman
open Freiman
namespace SourceMemo16_99
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,99,[1],([2],[3]),true,[(([1],[]),false),(([],[1]),false)],([1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound297,sourceBound872,sourceBound1187,sourceBound438,sourceBound860,sourceBound875,sourceBound1180,sourceBound292],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound297,sourceBound872,sourceBound298,sourceBound874,sourceBound864,sourceBound1188,sourceBound438,sourceBound860,sourceBound875,sourceBound1180,sourceBound292]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound297,sourceBound872,sourceBound1187,sourceBound438,sourceBound860,sourceBound875,sourceBound1180,sourceBound292].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound293,sourceBound857,sourceBound297,sourceBound872,sourceBound298,sourceBound874,sourceBound864,sourceBound1188,sourceBound438,sourceBound860,sourceBound875,sourceBound1180,sourceBound292].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_99.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b260 := sourceBound260) (b292 := sourceBound292) (b293 := sourceBound293) (b297 := sourceBound297) (b298 := sourceBound298) (b371 := sourceBound371) (b438 := sourceBound438) (b440 := sourceBound440) (b843 := sourceBound843) (b857 := sourceBound857) (b860 := sourceBound860) (b864 := sourceBound864) (b872 := sourceBound872) (b874 := sourceBound874) (b875 := sourceBound875) (b1180 := sourceBound1180) (b1187 := sourceBound1187) (b1188 := sourceBound1188)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG6.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG7.2.2.2.2.1) (BindingSourceBranches16.branchesG7.2.2.2.2.2.1) BindingNumeric16.norm48 BindingNumeric16.norm52 BindingNumeric16.pullKey123 BindingNumeric16.pull140 BindingNumeric16.pullKey124 BindingNumeric16.pullKey125 BindingNumeric16.pullKey126 BindingNumeric16.norm53 BindingNumeric16.pullKey8 BindingNumeric16.pullKey9 BindingNumeric16.pullKey10 eraseActual0 eraseActual1)
end SourceMemo16_99

open Freiman
open Freiman
namespace SourceMemo16_100
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,100,[2],([2],[3]),false,[(([3],[1]),true)],([2,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound276,sourceBound804,sourceBound862,sourceBound1142]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : ([sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound276,sourceBound804,sourceBound862,sourceBound1142] ++ [sourceBound276]).eraseDups = expected[0] := by
  have hdup : sourceBound276 ∈ expected[0] := by simp [expected]
  change (expected[0] ++ [sourceBound276]).eraseDups = expected[0]
  rw [List.eraseDups_append, erase0,
    BindingSourceSupport16.singleton_removeAll_of_mem hdup,
    List.eraseDups_nil, List.append_nil]
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_100.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b21 := sourceBound21) (b260 := sourceBound260) (b275 := sourceBound275) (b276 := sourceBound276) (b371 := sourceBound371) (b440 := sourceBound440) (b442 := sourceBound442) (b804 := sourceBound804) (b843 := sourceBound843) (b856 := sourceBound856) (b862 := sourceBound862) (b1142 := sourceBound1142)
      BindingSourceSupport16.relaxed2 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG7.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG7.2.2.2.2.2.2.2) BindingNumeric16.norm0 BindingNumeric16.pullKey127 BindingNumeric16.pullKey128 BindingNumeric16.norm54 BindingNumeric16.pullKey117 BindingNumeric16.pullKey118 BindingNumeric16.pullKey119 eraseActual0)
end SourceMemo16_100


open Freiman
namespace BatchLookup16
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
private def path96 : LowerHistoryPath := ⟨.left,96,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩

private theorem records96 : lowerHistoryRecordsFor path96 = [⟨.left,96,0,(-1),false,10,225⟩] := by
  change lowerHistoryRecordsFor (⟨.left,96,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 96, lowerHistoryRecordsL_list] <;> rfl


private def path97 : LowerHistoryPath := ⟨.left,97,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩

private theorem records97 : lowerHistoryRecordsFor path97 = [⟨.left,97,0,(-1),false,4,231⟩,⟨.left,97,1,(-1),false,2,231⟩,⟨.left,97,2,(-1),false,3,231⟩,⟨.left,97,3,(-1),false,1,231⟩] := by
  change lowerHistoryRecordsFor (⟨.left,97,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 97, lowerHistoryRecordsL_list] <;> rfl


private def path98 : LowerHistoryPath := ⟨.left,98,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩

private theorem records98 : lowerHistoryRecordsFor path98 = [⟨.left,98,0,(-1),false,6,237⟩,⟨.left,98,1,(-1),false,5,237⟩] := by
  change lowerHistoryRecordsFor (⟨.left,98,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 98, lowerHistoryRecordsL_list] <;> rfl


private def path99 : LowerHistoryPath := ⟨.left,99,[1],([2],[3]),true,[(([1],[]),false),(([],[1]),false)],([1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩

private theorem records99 : lowerHistoryRecordsFor path99 = [⟨.left,99,0,(-1),false,516,290⟩,⟨.left,99,1,(-1),false,515,296⟩] := by
  change lowerHistoryRecordsFor (⟨.left,99,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 99, lowerHistoryRecordsL_list] <;> rfl


private def path100 : LowerHistoryPath := ⟨.left,100,[2],([2],[3]),false,[(([3],[1]),true)],([2,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩

private theorem records100 : lowerHistoryRecordsFor path100 = [⟨.left,100,0,(-1),false,494,1185⟩] := by
  change lowerHistoryRecordsFor (⟨.left,100,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 100, lowerHistoryRecordsL_list] <;> rfl


end BatchLookup16

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

namespace BoundCompact16
open Freiman

end BoundCompact16

namespace BatchLookup15
open Freiman

private theorem bound2 :
    lowerHistoryBound 2 = sourceBound2 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[1]? = some sourceBound2 :=
    Eq.refl (some sourceBound2)
  exact (BoundCompact16.global_to_chunk1 1 (by decide)).trans hlocal

private theorem bound3 :
    lowerHistoryBound 3 = sourceBound3 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[2]? = some sourceBound3 :=
    Eq.refl (some sourceBound3)
  exact (BoundCompact16.global_to_chunk1 2 (by decide)).trans hlocal

private theorem bound21 :
    lowerHistoryBound 21 = sourceBound21 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[20]? = some sourceBound21 :=
    Eq.refl (some sourceBound21)
  exact (BoundCompact16.global_to_chunk1 20 (by decide)).trans hlocal

private theorem bound236 :
    lowerHistoryBound 236 = sourceBound236 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[35]? = some sourceBound236 :=
    Eq.refl (some sourceBound236)
  exact (BoundCompact16.global_to_chunk2 35 (by decide)).trans hlocal

private theorem bound244 :
    lowerHistoryBound 244 = sourceBound244 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[43]? = some sourceBound244 :=
    Eq.refl (some sourceBound244)
  exact (BoundCompact16.global_to_chunk2 43 (by decide)).trans hlocal

private theorem bound260 :
    lowerHistoryBound 260 = sourceBound260 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[59]? = some sourceBound260 :=
    Eq.refl (some sourceBound260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hlocal

private theorem bound262 :
    lowerHistoryBound 262 = sourceBound262 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[61]? = some sourceBound262 :=
    Eq.refl (some sourceBound262)
  exact (BoundCompact16.global_to_chunk2 61 (by decide)).trans hlocal

private theorem bound266 :
    lowerHistoryBound 266 = sourceBound266 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[65]? = some sourceBound266 :=
    Eq.refl (some sourceBound266)
  exact (BoundCompact16.global_to_chunk2 65 (by decide)).trans hlocal

private theorem bound270 :
    lowerHistoryBound 270 = sourceBound270 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[69]? = some sourceBound270 :=
    Eq.refl (some sourceBound270)
  exact (BoundCompact16.global_to_chunk2 69 (by decide)).trans hlocal

private theorem bound274 :
    lowerHistoryBound 274 = sourceBound274 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[73]? = some sourceBound274 :=
    Eq.refl (some sourceBound274)
  exact (BoundCompact16.global_to_chunk2 73 (by decide)).trans hlocal

private theorem bound275 :
    lowerHistoryBound 275 = sourceBound275 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[74]? = some sourceBound275 :=
    Eq.refl (some sourceBound275)
  exact (BoundCompact16.global_to_chunk2 74 (by decide)).trans hlocal

private theorem bound276 :
    lowerHistoryBound 276 = sourceBound276 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[75]? = some sourceBound276 :=
    Eq.refl (some sourceBound276)
  exact (BoundCompact16.global_to_chunk2 75 (by decide)).trans hlocal

private theorem bound286 :
    lowerHistoryBound 286 = sourceBound286 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[85]? = some sourceBound286 :=
    Eq.refl (some sourceBound286)
  exact (BoundCompact16.global_to_chunk2 85 (by decide)).trans hlocal

private theorem bound371 :
    lowerHistoryBound 371 = sourceBound371 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[170]? = some sourceBound371 :=
    Eq.refl (some sourceBound371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hlocal

private theorem bound414 :
    lowerHistoryBound 414 = sourceBound414 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[13]? = some sourceBound414 :=
    Eq.refl (some sourceBound414)
  exact (BoundCompact16.global_to_chunk3 13 (by decide)).trans hlocal

private theorem bound417 :
    lowerHistoryBound 417 = sourceBound417 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[16]? = some sourceBound417 :=
    Eq.refl (some sourceBound417)
  exact (BoundCompact16.global_to_chunk3 16 (by decide)).trans hlocal

private theorem bound418 :
    lowerHistoryBound 418 = sourceBound418 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[17]? = some sourceBound418 :=
    Eq.refl (some sourceBound418)
  exact (BoundCompact16.global_to_chunk3 17 (by decide)).trans hlocal

private theorem bound423 :
    lowerHistoryBound 423 = sourceBound423 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[22]? = some sourceBound423 :=
    Eq.refl (some sourceBound423)
  exact (BoundCompact16.global_to_chunk3 22 (by decide)).trans hlocal

private theorem bound426 :
    lowerHistoryBound 426 = sourceBound426 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[25]? = some sourceBound426 :=
    Eq.refl (some sourceBound426)
  exact (BoundCompact16.global_to_chunk3 25 (by decide)).trans hlocal

private theorem bound440 :
    lowerHistoryBound 440 = sourceBound440 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[39]? = some sourceBound440 :=
    Eq.refl (some sourceBound440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hlocal

private theorem bound442 :
    lowerHistoryBound 442 = sourceBound442 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[41]? = some sourceBound442 :=
    Eq.refl (some sourceBound442)
  exact (BoundCompact16.global_to_chunk3 41 (by decide)).trans hlocal

private theorem bound736 :
    lowerHistoryBound 736 = sourceBound736 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[135]? = some sourceBound736 :=
    Eq.refl (some sourceBound736)
  exact (BoundCompact16.global_to_chunk4 135 (by decide)).trans hlocal

private theorem bound747 :
    lowerHistoryBound 747 = sourceBound747 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[146]? = some sourceBound747 :=
    Eq.refl (some sourceBound747)
  exact (BoundCompact16.global_to_chunk4 146 (by decide)).trans hlocal

private theorem bound752 :
    lowerHistoryBound 752 = sourceBound752 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[151]? = some sourceBound752 :=
    Eq.refl (some sourceBound752)
  exact (BoundCompact16.global_to_chunk4 151 (by decide)).trans hlocal

private theorem bound763 :
    lowerHistoryBound 763 = sourceBound763 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[162]? = some sourceBound763 :=
    Eq.refl (some sourceBound763)
  exact (BoundCompact16.global_to_chunk4 162 (by decide)).trans hlocal

private theorem bound779 :
    lowerHistoryBound 779 = sourceBound779 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[178]? = some sourceBound779 :=
    Eq.refl (some sourceBound779)
  exact (BoundCompact16.global_to_chunk4 178 (by decide)).trans hlocal

private theorem bound782 :
    lowerHistoryBound 782 = sourceBound782 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[181]? = some sourceBound782 :=
    Eq.refl (some sourceBound782)
  exact (BoundCompact16.global_to_chunk4 181 (by decide)).trans hlocal

private theorem bound804 :
    lowerHistoryBound 804 = sourceBound804 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[3]? = some sourceBound804 :=
    Eq.refl (some sourceBound804)
  exact (BoundCompact16.global_to_chunk5 3 (by decide)).trans hlocal

private theorem bound805 :
    lowerHistoryBound 805 = sourceBound805 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[4]? = some sourceBound805 :=
    Eq.refl (some sourceBound805)
  exact (BoundCompact16.global_to_chunk5 4 (by decide)).trans hlocal

private theorem bound809 :
    lowerHistoryBound 809 = sourceBound809 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[8]? = some sourceBound809 :=
    Eq.refl (some sourceBound809)
  exact (BoundCompact16.global_to_chunk5 8 (by decide)).trans hlocal

private theorem bound813 :
    lowerHistoryBound 813 = sourceBound813 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[12]? = some sourceBound813 :=
    Eq.refl (some sourceBound813)
  exact (BoundCompact16.global_to_chunk5 12 (by decide)).trans hlocal

private theorem bound829 :
    lowerHistoryBound 829 = sourceBound829 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[28]? = some sourceBound829 :=
    Eq.refl (some sourceBound829)
  exact (BoundCompact16.global_to_chunk5 28 (by decide)).trans hlocal

private theorem bound831 :
    lowerHistoryBound 831 = sourceBound831 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[30]? = some sourceBound831 :=
    Eq.refl (some sourceBound831)
  exact (BoundCompact16.global_to_chunk5 30 (by decide)).trans hlocal

private theorem bound843 :
    lowerHistoryBound 843 = sourceBound843 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[42]? = some sourceBound843 :=
    Eq.refl (some sourceBound843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hlocal

private theorem bound846 :
    lowerHistoryBound 846 = sourceBound846 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[45]? = some sourceBound846 :=
    Eq.refl (some sourceBound846)
  exact (BoundCompact16.global_to_chunk5 45 (by decide)).trans hlocal

private theorem bound851 :
    lowerHistoryBound 851 = sourceBound851 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[50]? = some sourceBound851 :=
    Eq.refl (some sourceBound851)
  exact (BoundCompact16.global_to_chunk5 50 (by decide)).trans hlocal

private theorem bound853 :
    lowerHistoryBound 853 = sourceBound853 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[52]? = some sourceBound853 :=
    Eq.refl (some sourceBound853)
  exact (BoundCompact16.global_to_chunk5 52 (by decide)).trans hlocal

private theorem bound856 :
    lowerHistoryBound 856 = sourceBound856 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[55]? = some sourceBound856 :=
    Eq.refl (some sourceBound856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hlocal

private theorem bound862 :
    lowerHistoryBound 862 = sourceBound862 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[61]? = some sourceBound862 :=
    Eq.refl (some sourceBound862)
  exact (BoundCompact16.global_to_chunk5 61 (by decide)).trans hlocal

private theorem bound878 :
    lowerHistoryBound 878 = sourceBound878 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[77]? = some sourceBound878 :=
    Eq.refl (some sourceBound878)
  exact (BoundCompact16.global_to_chunk5 77 (by decide)).trans hlocal

private theorem bound1071 :
    lowerHistoryBound 1071 = sourceBound1071 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[70]? = some sourceBound1071 :=
    Eq.refl (some sourceBound1071)
  exact (BoundCompact16.global_to_chunk6 70).trans hlocal

private theorem bound1093 :
    lowerHistoryBound 1093 = sourceBound1093 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[92]? = some sourceBound1093 :=
    Eq.refl (some sourceBound1093)
  exact (BoundCompact16.global_to_chunk6 92).trans hlocal

private theorem bound1117 :
    lowerHistoryBound 1117 = sourceBound1117 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[116]? = some sourceBound1117 :=
    Eq.refl (some sourceBound1117)
  exact (BoundCompact16.global_to_chunk6 116).trans hlocal

private theorem bound1132 :
    lowerHistoryBound 1132 = sourceBound1132 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[131]? = some sourceBound1132 :=
    Eq.refl (some sourceBound1132)
  exact (BoundCompact16.global_to_chunk6 131).trans hlocal

private theorem bound1142 :
    lowerHistoryBound 1142 = sourceBound1142 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[141]? = some sourceBound1142 :=
    Eq.refl (some sourceBound1142)
  exact (BoundCompact16.global_to_chunk6 141).trans hlocal

private theorem bound1145 :
    lowerHistoryBound 1145 = sourceBound1145 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[144]? = some sourceBound1145 :=
    Eq.refl (some sourceBound1145)
  exact (BoundCompact16.global_to_chunk6 144).trans hlocal

private theorem bound1152 :
    lowerHistoryBound 1152 = sourceBound1152 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[151]? = some sourceBound1152 :=
    Eq.refl (some sourceBound1152)
  exact (BoundCompact16.global_to_chunk6 151).trans hlocal

private theorem bound1155 :
    lowerHistoryBound 1155 = sourceBound1155 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[154]? = some sourceBound1155 :=
    Eq.refl (some sourceBound1155)
  exact (BoundCompact16.global_to_chunk6 154).trans hlocal

private theorem bound1164 :
    lowerHistoryBound 1164 = sourceBound1164 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[163]? = some sourceBound1164 :=
    Eq.refl (some sourceBound1164)
  exact (BoundCompact16.global_to_chunk6 163).trans hlocal

private theorem bound1173 :
    lowerHistoryBound 1173 = sourceBound1173 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[172]? = some sourceBound1173 :=
    Eq.refl (some sourceBound1173)
  exact (BoundCompact16.global_to_chunk6 172).trans hlocal

end BatchLookup15

namespace BatchLookup16
open Freiman

private theorem bound1 :
    lowerHistoryBound 1 = sourceBound1 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[0]? = some sourceBound1 :=
    Eq.refl (some sourceBound1)
  exact (BoundCompact16.global_to_chunk1 0 (by decide)).trans hlocal

private theorem bound292 :
    lowerHistoryBound 292 = sourceBound292 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[91]? = some sourceBound292 :=
    Eq.refl (some sourceBound292)
  exact (BoundCompact16.global_to_chunk2 91 (by decide)).trans hlocal

private theorem bound293 :
    lowerHistoryBound 293 = sourceBound293 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[92]? = some sourceBound293 :=
    Eq.refl (some sourceBound293)
  exact (BoundCompact16.global_to_chunk2 92 (by decide)).trans hlocal

private theorem bound297 :
    lowerHistoryBound 297 = sourceBound297 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[96]? = some sourceBound297 :=
    Eq.refl (some sourceBound297)
  exact (BoundCompact16.global_to_chunk2 96 (by decide)).trans hlocal

private theorem bound298 :
    lowerHistoryBound 298 = sourceBound298 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[97]? = some sourceBound298 :=
    Eq.refl (some sourceBound298)
  exact (BoundCompact16.global_to_chunk2 97 (by decide)).trans hlocal

private theorem bound438 :
    lowerHistoryBound 438 = sourceBound438 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[37]? = some sourceBound438 :=
    Eq.refl (some sourceBound438)
  exact (BoundCompact16.global_to_chunk3 37 (by decide)).trans hlocal

private theorem bound857 :
    lowerHistoryBound 857 = sourceBound857 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[56]? = some sourceBound857 :=
    Eq.refl (some sourceBound857)
  exact (BoundCompact16.global_to_chunk5 56 (by decide)).trans hlocal

private theorem bound860 :
    lowerHistoryBound 860 = sourceBound860 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[59]? = some sourceBound860 :=
    Eq.refl (some sourceBound860)
  exact (BoundCompact16.global_to_chunk5 59 (by decide)).trans hlocal

private theorem bound864 :
    lowerHistoryBound 864 = sourceBound864 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[63]? = some sourceBound864 :=
    Eq.refl (some sourceBound864)
  exact (BoundCompact16.global_to_chunk5 63 (by decide)).trans hlocal

private theorem bound867 :
    lowerHistoryBound 867 = sourceBound867 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[66]? = some sourceBound867 :=
    Eq.refl (some sourceBound867)
  exact (BoundCompact16.global_to_chunk5 66 (by decide)).trans hlocal

private theorem bound872 :
    lowerHistoryBound 872 = sourceBound872 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[71]? = some sourceBound872 :=
    Eq.refl (some sourceBound872)
  exact (BoundCompact16.global_to_chunk5 71 (by decide)).trans hlocal

private theorem bound874 :
    lowerHistoryBound 874 = sourceBound874 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[73]? = some sourceBound874 :=
    Eq.refl (some sourceBound874)
  exact (BoundCompact16.global_to_chunk5 73 (by decide)).trans hlocal

private theorem bound875 :
    lowerHistoryBound 875 = sourceBound875 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[74]? = some sourceBound875 :=
    Eq.refl (some sourceBound875)
  exact (BoundCompact16.global_to_chunk5 74 (by decide)).trans hlocal

private theorem bound1180 :
    lowerHistoryBound 1180 = sourceBound1180 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[179]? = some sourceBound1180 :=
    Eq.refl (some sourceBound1180)
  exact (BoundCompact16.global_to_chunk6 179).trans hlocal

private theorem bound1187 :
    lowerHistoryBound 1187 = sourceBound1187 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[186]? = some sourceBound1187 :=
    Eq.refl (some sourceBound1187)
  exact (BoundCompact16.global_to_chunk6 186).trans hlocal

private theorem bound1188 :
    lowerHistoryBound 1188 = sourceBound1188 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[187]? = some sourceBound1188 :=
    Eq.refl (some sourceBound1188)
  exact (BoundCompact16.global_to_chunk6 187).trans hlocal

end BatchLookup16


-- Source: agents.batch16.SourceValuesAll
open Freiman
namespace SourceValues16
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem source96 : lowerHistorySourcePremises BatchLookup16.path96 =
    ([[371,843,260,440,3,293,857,867,1,851,2,1152,426,752,1132,423,736,809,1071,262]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup16.bound293 (congrArg₂ List.cons BatchLookup16.bound857 (congrArg₂ List.cons BatchLookup16.bound867 (congrArg₂ List.cons BatchLookup16.bound1 (congrArg₂ List.cons BatchLookup15.bound851 (congrArg₂ List.cons BatchLookup15.bound2 (congrArg₂ List.cons BatchLookup15.bound1152 (congrArg₂ List.cons BatchLookup15.bound426 (congrArg₂ List.cons BatchLookup15.bound752 (congrArg₂ List.cons BatchLookup15.bound1132 (congrArg₂ List.cons BatchLookup15.bound423 (congrArg₂ List.cons BatchLookup15.bound736 (congrArg₂ List.cons BatchLookup15.bound809 (congrArg₂ List.cons BatchLookup15.bound1071 (congrArg₂ List.cons BatchLookup15.bound262 (rfl : ([] : List CertBound) = []))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo16_96.source.trans hb.symm
private theorem length96 : BatchLookup16.path96.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path96).length := by
  exact (congrArg List.length source96).symm
private theorem source97 : lowerHistorySourcePremises BatchLookup16.path97 =
    ([[371,843,260,440,3,293,857,867,1,851,2,1152,418,779,1145,414,747,829,1093,236],[371,843,260,440,3,293,857,867,1,851,2,1152,418,779,266,813,763,1155,414,747,829,1093,236],[371,843,260,440,3,293,857,867,1,851,2,274,878,418,779,1145,414,747,829,1093,236],[371,843,260,440,3,293,857,867,1,851,2,274,878,418,779,266,813,763,1155,414,747,829,1093,236]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup16.bound293 (congrArg₂ List.cons BatchLookup16.bound857 (congrArg₂ List.cons BatchLookup16.bound867 (congrArg₂ List.cons BatchLookup16.bound1 (congrArg₂ List.cons BatchLookup15.bound851 (congrArg₂ List.cons BatchLookup15.bound2 (congrArg₂ List.cons BatchLookup15.bound1152 (congrArg₂ List.cons BatchLookup15.bound418 (congrArg₂ List.cons BatchLookup15.bound779 (congrArg₂ List.cons BatchLookup15.bound1145 (congrArg₂ List.cons BatchLookup15.bound414 (congrArg₂ List.cons BatchLookup15.bound747 (congrArg₂ List.cons BatchLookup15.bound829 (congrArg₂ List.cons BatchLookup15.bound1093 (congrArg₂ List.cons BatchLookup15.bound236 (rfl : ([] : List CertBound) = []))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup16.bound293 (congrArg₂ List.cons BatchLookup16.bound857 (congrArg₂ List.cons BatchLookup16.bound867 (congrArg₂ List.cons BatchLookup16.bound1 (congrArg₂ List.cons BatchLookup15.bound851 (congrArg₂ List.cons BatchLookup15.bound2 (congrArg₂ List.cons BatchLookup15.bound1152 (congrArg₂ List.cons BatchLookup15.bound418 (congrArg₂ List.cons BatchLookup15.bound779 (congrArg₂ List.cons BatchLookup15.bound266 (congrArg₂ List.cons BatchLookup15.bound813 (congrArg₂ List.cons BatchLookup15.bound763 (congrArg₂ List.cons BatchLookup15.bound1155 (congrArg₂ List.cons BatchLookup15.bound414 (congrArg₂ List.cons BatchLookup15.bound747 (congrArg₂ List.cons BatchLookup15.bound829 (congrArg₂ List.cons BatchLookup15.bound1093 (congrArg₂ List.cons BatchLookup15.bound236 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup16.bound293 (congrArg₂ List.cons BatchLookup16.bound857 (congrArg₂ List.cons BatchLookup16.bound867 (congrArg₂ List.cons BatchLookup16.bound1 (congrArg₂ List.cons BatchLookup15.bound851 (congrArg₂ List.cons BatchLookup15.bound2 (congrArg₂ List.cons BatchLookup15.bound274 (congrArg₂ List.cons BatchLookup15.bound878 (congrArg₂ List.cons BatchLookup15.bound418 (congrArg₂ List.cons BatchLookup15.bound779 (congrArg₂ List.cons BatchLookup15.bound1145 (congrArg₂ List.cons BatchLookup15.bound414 (congrArg₂ List.cons BatchLookup15.bound747 (congrArg₂ List.cons BatchLookup15.bound829 (congrArg₂ List.cons BatchLookup15.bound1093 (congrArg₂ List.cons BatchLookup15.bound236 (rfl : ([] : List CertBound) = [])))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup16.bound293 (congrArg₂ List.cons BatchLookup16.bound857 (congrArg₂ List.cons BatchLookup16.bound867 (congrArg₂ List.cons BatchLookup16.bound1 (congrArg₂ List.cons BatchLookup15.bound851 (congrArg₂ List.cons BatchLookup15.bound2 (congrArg₂ List.cons BatchLookup15.bound274 (congrArg₂ List.cons BatchLookup15.bound878 (congrArg₂ List.cons BatchLookup15.bound418 (congrArg₂ List.cons BatchLookup15.bound779 (congrArg₂ List.cons BatchLookup15.bound266 (congrArg₂ List.cons BatchLookup15.bound813 (congrArg₂ List.cons BatchLookup15.bound763 (congrArg₂ List.cons BatchLookup15.bound1155 (congrArg₂ List.cons BatchLookup15.bound414 (congrArg₂ List.cons BatchLookup15.bound747 (congrArg₂ List.cons BatchLookup15.bound829 (congrArg₂ List.cons BatchLookup15.bound1093 (congrArg₂ List.cons BatchLookup15.bound236 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))))
  exact SourceMemo16_97.source.trans hb.symm
private theorem length97 : BatchLookup16.path97.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path97).length := by
  exact (congrArg List.length source97).symm
private theorem source98 : lowerHistorySourcePremises BatchLookup16.path98 =
    ([[371,843,260,440,3,293,857,867,1,851,2,270,831,1164,417,782,853,1117,244],[371,843,260,440,3,293,857,867,1,851,2,270,831,286,846,805,1173,417,782,853,1117,244]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup16.bound293 (congrArg₂ List.cons BatchLookup16.bound857 (congrArg₂ List.cons BatchLookup16.bound867 (congrArg₂ List.cons BatchLookup16.bound1 (congrArg₂ List.cons BatchLookup15.bound851 (congrArg₂ List.cons BatchLookup15.bound2 (congrArg₂ List.cons BatchLookup15.bound270 (congrArg₂ List.cons BatchLookup15.bound831 (congrArg₂ List.cons BatchLookup15.bound1164 (congrArg₂ List.cons BatchLookup15.bound417 (congrArg₂ List.cons BatchLookup15.bound782 (congrArg₂ List.cons BatchLookup15.bound853 (congrArg₂ List.cons BatchLookup15.bound1117 (congrArg₂ List.cons BatchLookup15.bound244 (rfl : ([] : List CertBound) = [])))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup16.bound293 (congrArg₂ List.cons BatchLookup16.bound857 (congrArg₂ List.cons BatchLookup16.bound867 (congrArg₂ List.cons BatchLookup16.bound1 (congrArg₂ List.cons BatchLookup15.bound851 (congrArg₂ List.cons BatchLookup15.bound2 (congrArg₂ List.cons BatchLookup15.bound270 (congrArg₂ List.cons BatchLookup15.bound831 (congrArg₂ List.cons BatchLookup15.bound286 (congrArg₂ List.cons BatchLookup15.bound846 (congrArg₂ List.cons BatchLookup15.bound805 (congrArg₂ List.cons BatchLookup15.bound1173 (congrArg₂ List.cons BatchLookup15.bound417 (congrArg₂ List.cons BatchLookup15.bound782 (congrArg₂ List.cons BatchLookup15.bound853 (congrArg₂ List.cons BatchLookup15.bound1117 (congrArg₂ List.cons BatchLookup15.bound244 (rfl : ([] : List CertBound) = []))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))
  exact SourceMemo16_98.source.trans hb.symm
private theorem length98 : BatchLookup16.path98.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path98).length := by
  exact (congrArg List.length source98).symm
private theorem source99 : lowerHistorySourcePremises BatchLookup16.path99 =
    ([[371,843,260,440,3,293,857,297,872,1187,438,860,875,1180,292],[371,843,260,440,3,293,857,297,872,298,874,864,1188,438,860,875,1180,292]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup16.bound293 (congrArg₂ List.cons BatchLookup16.bound857 (congrArg₂ List.cons BatchLookup16.bound297 (congrArg₂ List.cons BatchLookup16.bound872 (congrArg₂ List.cons BatchLookup16.bound1187 (congrArg₂ List.cons BatchLookup16.bound438 (congrArg₂ List.cons BatchLookup16.bound860 (congrArg₂ List.cons BatchLookup16.bound875 (congrArg₂ List.cons BatchLookup16.bound1180 (congrArg₂ List.cons BatchLookup16.bound292 (rfl : ([] : List CertBound) = [])))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup16.bound293 (congrArg₂ List.cons BatchLookup16.bound857 (congrArg₂ List.cons BatchLookup16.bound297 (congrArg₂ List.cons BatchLookup16.bound872 (congrArg₂ List.cons BatchLookup16.bound298 (congrArg₂ List.cons BatchLookup16.bound874 (congrArg₂ List.cons BatchLookup16.bound864 (congrArg₂ List.cons BatchLookup16.bound1188 (congrArg₂ List.cons BatchLookup16.bound438 (congrArg₂ List.cons BatchLookup16.bound860 (congrArg₂ List.cons BatchLookup16.bound875 (congrArg₂ List.cons BatchLookup16.bound1180 (congrArg₂ List.cons BatchLookup16.bound292 (rfl : ([] : List CertBound) = []))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))
  exact SourceMemo16_99.source.trans hb.symm
private theorem length99 : BatchLookup16.path99.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path99).length := by
  exact (congrArg List.length source99).symm
private theorem source100 : lowerHistorySourcePremises BatchLookup16.path100 =
    ([[371,843,260,440,3,856,21,275,442,276,804,862,1142]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup15.bound275 (congrArg₂ List.cons BatchLookup15.bound442 (congrArg₂ List.cons BatchLookup15.bound276 (congrArg₂ List.cons BatchLookup15.bound804 (congrArg₂ List.cons BatchLookup15.bound862 (congrArg₂ List.cons BatchLookup15.bound1142 (rfl : ([] : List CertBound) = [])))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo16_100.source.trans hb.symm
private theorem length100 : BatchLookup16.path100.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path100).length := by
  exact (congrArg List.length source100).symm
end SourceValues16



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
namespace BatchLookup16
set_option maxRecDepth 30000
private theorem size01 : lowerHistoryPremises01.size = 200 := by rfl
private theorem size02 : lowerHistoryPremises02.size = 200 := by rfl
private theorem size03 : lowerHistoryPremises03.size = 200 := by rfl
private theorem size04 : lowerHistoryPremises04.size = 200 := by rfl
private theorem size05 : lowerHistoryPremises05.size = 200 := by rfl
private theorem premise1 : lowerHistoryPremises[0]? = some ([1, 2, 3, 236, 260, 266, 274, 293, 371, 414, 418, 440, 747, 763, 779, 813, 829, 843, 851, 857, 867, 878, 1093, 1155] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 0 = 0+0 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 0 (by decide)]
  rfl

private theorem premise2 : lowerHistoryPremises[1]? = some ([1, 2, 3, 236, 260, 266, 293, 371, 414, 418, 440, 747, 763, 779, 813, 829, 843, 851, 857, 867, 1093, 1152, 1155] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 1 = 0+1 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 1 (by decide)]
  rfl

private theorem premise3 : lowerHistoryPremises[2]? = some ([1, 2, 3, 236, 260, 274, 293, 371, 414, 418, 440, 747, 779, 829, 843, 851, 857, 867, 878, 1093, 1145] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 2 = 0+2 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 2 (by decide)]
  rfl

private theorem premise4 : lowerHistoryPremises[3]? = some ([1, 2, 3, 236, 260, 293, 371, 414, 418, 440, 747, 779, 829, 843, 851, 857, 867, 1093, 1145, 1152] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 3 = 0+3 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 3 (by decide)]
  rfl

private theorem premise5 : lowerHistoryPremises[4]? = some ([1, 2, 3, 244, 260, 270, 286, 293, 371, 417, 440, 782, 805, 831, 843, 846, 851, 853, 857, 867, 1117, 1173] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 4 = 0+4 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 4 (by decide)]
  rfl

private theorem premise6 : lowerHistoryPremises[5]? = some ([1, 2, 3, 244, 260, 270, 293, 371, 417, 440, 782, 831, 843, 851, 853, 857, 867, 1117, 1164] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 5 = 0+5 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 5 (by decide)]
  rfl

private theorem premise10 : lowerHistoryPremises[9]? = some ([1, 2, 3, 260, 262, 293, 371, 423, 426, 440, 736, 752, 809, 843, 851, 857, 867, 1071, 1132, 1152] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 9 = 0+9 by decide]
  rw [PremiseCompact50.lookup_chunk1 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 9 (by decide)]
  rfl

private theorem premise494 : lowerHistoryPremises[493]? = some ([3, 21, 260, 275, 276, 371, 440, 442, 804, 843, 856, 862, 1142] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 493 = 400+93 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 93 (by decide)]
  rfl

private theorem premise515 : lowerHistoryPremises[514]? = some ([3, 260, 292, 293, 297, 298, 371, 438, 440, 843, 857, 860, 864, 872, 874, 875, 1180, 1188] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 514 = 400+114 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 114 (by decide)]
  rfl

private theorem premise516 : lowerHistoryPremises[515]? = some ([3, 260, 292, 293, 297, 371, 438, 440, 843, 857, 860, 872, 875, 1180, 1187] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 515 = 400+115 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 115 (by decide)]
  rfl

end BatchLookup16

-- Source: agents.batch15.Coverage
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

-- Source: agents.batch16.CoverageAll
open Freiman BatchLookup16 BatchCoverage15
namespace BatchCoverageAll16
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem coverage96 : (List.range path96.alternatives).all
    (coverageCheck path96 ([⟨.left,96,0,(-1),false,10,225⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage97 : (List.range path97.alternatives).all
    (coverageCheck path97 ([⟨.left,97,0,(-1),false,4,231⟩,⟨.left,97,1,(-1),false,2,231⟩,⟨.left,97,2,(-1),false,3,231⟩,⟨.left,97,3,(-1),false,1,231⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage98 : (List.range path98.alternatives).all
    (coverageCheck path98 ([⟨.left,98,0,(-1),false,6,237⟩,⟨.left,98,1,(-1),false,5,237⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage99 : (List.range path99.alternatives).all
    (coverageCheck path99 ([⟨.left,99,0,(-1),false,516,290⟩,⟨.left,99,1,(-1),false,515,296⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage100 : (List.range path100.alternatives).all
    (coverageCheck path100 ([⟨.left,100,0,(-1),false,494,1185⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
end BatchCoverageAll16


open Freiman BatchLookup16
namespace PathLookup16
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
private theorem pathsL_slice : (lowerHistoryPathsL.toList.drop 50).take 50 = [
⟨.left,51,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,52,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,53,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),false)],([1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,54,[1],([2],[3]),false,[(([1],[]),false),(([3],[1]),true),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,3⟩,
⟨.left,55,[1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([3],[]),true)],([1,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,3⟩,
⟨.left,56,[1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([2],[]),true)],([1,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,3⟩,
⟨.left,57,[1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),true)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,3⟩,
⟨.left,58,[1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,12⟩,
⟨.left,59,[1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,6⟩,
⟨.left,60,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),true),(([],[1]),false)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,61,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([3],[]),true)],([1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,62,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([2],[]),true)],([1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,63,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),true)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,64,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,65,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,66,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,67,[1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,68,[1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,69,[1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,70,[1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([3],[]),true)],([1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,71,[1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([2],[]),true)],([1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,72,[1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([1],[]),true)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,73,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([3],[]),true)],([1,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,74,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([2],[]),true)],([1,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,75,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,76,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,77,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,78,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),false),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,79,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([3],[]),true)],([1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,80,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([2],[]),true)],([1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,81,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),true)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,82,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,83,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,84,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,85,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),false),(([],[1]),false)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,86,[1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([3],[]),true)],([1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,87,[1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([2],[]),true)],([1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,88,[1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),true)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,89,[1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,90,[1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,91,[1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,92,[1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),false),(([],[1]),false)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,93,[1],([2],[3]),true,[(([1],[]),true),(([3],[]),true)],([1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,94,[1],([2],[3]),true,[(([1],[]),true),(([2],[]),true)],([1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,95,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),true)],([1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,96,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,97,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,98,[1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,99,[1],([2],[3]),true,[(([1],[]),false),(([],[1]),false)],([1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,100,[2],([2],[3]),false,[(([3],[1]),true)],([2,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩
] := by rfl
private theorem slice_get {α : Type} (xs : List α) (i : Nat) (hi : i < 50) :
    ((xs.drop 50).take 50)[i]? = xs[50+i]? := by
  simp [List.getElem?_take, List.getElem?_drop, hi]
private theorem path96_lookup : lowerHistoryPaths[95]? = some path96 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[45]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[95]? = some path96 :=
    (slice_get lowerHistoryPathsL.toList 45 (by decide)).symm.trans hs
  exact (first_lookup 95 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path97_lookup : lowerHistoryPaths[96]? = some path97 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[46]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[96]? = some path97 :=
    (slice_get lowerHistoryPathsL.toList 46 (by decide)).symm.trans hs
  exact (first_lookup 96 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path98_lookup : lowerHistoryPaths[97]? = some path98 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[47]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[97]? = some path98 :=
    (slice_get lowerHistoryPathsL.toList 47 (by decide)).symm.trans hs
  exact (first_lookup 97 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path99_lookup : lowerHistoryPaths[98]? = some path99 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[48]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[98]? = some path99 :=
    (slice_get lowerHistoryPathsL.toList 48 (by decide)).symm.trans hs
  exact (first_lookup 98 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path100_lookup : lowerHistoryPaths[99]? = some path100 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[49]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[99]? = some path100 :=
    (slice_get lowerHistoryPathsL.toList 49 (by decide)).symm.trans hs
  exact (first_lookup 99 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
end PathLookup16

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

end WitnessCompact16

namespace WitnessCompact16
open Freiman

end WitnessCompact16

namespace WitnessLookup15
open Freiman

end WitnessLookup15

namespace WitnessLookup16
open Freiman

private theorem witness225_projection :
    (lowerHistoryWitness 225).lowerBound = lowerHistoryBound 293 ∧
    (lowerHistoryWitness 225).upperBound = lowerHistoryBound 1071 ∧
    (lowerHistoryWitness 225).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[24]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 293, lowerHistoryBound 1071, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 293, lowerHistoryBound 1071, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk2 24 (by decide))).trans hl

private theorem witness231_projection :
    (lowerHistoryWitness 231).lowerBound = lowerHistoryBound 293 ∧
    (lowerHistoryWitness 231).upperBound = lowerHistoryBound 1093 ∧
    (lowerHistoryWitness 231).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[30]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 293, lowerHistoryBound 1093, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 293, lowerHistoryBound 1093, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk2 30 (by decide))).trans hl

private theorem witness237_projection :
    (lowerHistoryWitness 237).lowerBound = lowerHistoryBound 293 ∧
    (lowerHistoryWitness 237).upperBound = lowerHistoryBound 1117 ∧
    (lowerHistoryWitness 237).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[36]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 293, lowerHistoryBound 1117, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 293, lowerHistoryBound 1117, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk2 36 (by decide))).trans hl

private theorem witness290_projection :
    (lowerHistoryWitness 290).lowerBound = lowerHistoryBound 297 ∧
    (lowerHistoryWitness 290).upperBound = lowerHistoryBound 843 ∧
    (lowerHistoryWitness 290).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[89]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 297, lowerHistoryBound 843, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 297, lowerHistoryBound 843, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk2 89 (by decide))).trans hl

private theorem witness296_projection :
    (lowerHistoryWitness 296).lowerBound = lowerHistoryBound 298 ∧
    (lowerHistoryWitness 296).upperBound = lowerHistoryBound 843 ∧
    (lowerHistoryWitness 296).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses02[95]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 298, lowerHistoryBound 843, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 298, lowerHistoryBound 843, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk2 95 (by decide))).trans hl

private theorem witness1185_projection :
    (lowerHistoryWitness 1185).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1185).upperBound = lowerHistoryBound 1142 ∧
    (lowerHistoryWitness 1185).rectangle = (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[184]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1142, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1142, (⟨(1/3),(1/2),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk6 184)).trans hl

end WitnessLookup16



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

open Freiman BatchLookup16 BindingIds19
namespace BatchIdSolution50
set_option maxRecDepth 30000
set_option maxHeartbeats 0
private theorem premise_size : lowerHistoryPremises.size = 1025 := by
  simp only [lowerHistoryPremises, Array.size_append]
  rfl
private theorem witness_size : lowerHistoryWitnesses.size = 1194 := by
  simp only [lowerHistoryWitnesses, Array.size_append]
  rfl
private def wids : Nat → Nat × Nat
  | 66 => (286,1117)
  | 197 => (292,843)
  | 215 => (293,843)
  | 225 => (293,1071)
  | 231 => (293,1093)
  | 237 => (293,1117)
  | 243 => (293,1142)
  | 290 => (297,843)
  | 296 => (298,843)
  | 835 => (440,946)
  | 841 => (440,947)
  | 853 => (440,960)
  | 865 => (440,968)
  | 871 => (440,969)
  | 877 => (440,983)
  | 895 => (440,989)
  | 901 => (440,990)
  | 907 => (440,1015)
  | 919 => (440,1019)
  | 943 => (440,1026)
  | 949 => (440,1047)
  | 967 => (440,1064)
  | 979 => (440,1071)
  | 985 => (440,1086)
  | 997 => (440,1093)
  | 1005 => (440,1117)
  | 1185 => (442,1142)
  | _ => (0,0)
private def preIDs : Nat → List Nat
  | 1 => [1, 2, 3, 236, 260, 266, 274, 293, 371, 414, 418, 440, 747, 763, 779, 813, 829, 843, 851, 857, 867, 878, 1093, 1155]
  | 2 => [1, 2, 3, 236, 260, 266, 293, 371, 414, 418, 440, 747, 763, 779, 813, 829, 843, 851, 857, 867, 1093, 1152, 1155]
  | 3 => [1, 2, 3, 236, 260, 274, 293, 371, 414, 418, 440, 747, 779, 829, 843, 851, 857, 867, 878, 1093, 1145]
  | 4 => [1, 2, 3, 236, 260, 293, 371, 414, 418, 440, 747, 779, 829, 843, 851, 857, 867, 1093, 1145, 1152]
  | 5 => [1, 2, 3, 244, 260, 270, 286, 293, 371, 417, 440, 782, 805, 831, 843, 846, 851, 853, 857, 867, 1117, 1173]
  | 6 => [1, 2, 3, 244, 260, 270, 293, 371, 417, 440, 782, 831, 843, 851, 853, 857, 867, 1117, 1164]
  | 10 => [1, 2, 3, 260, 262, 293, 371, 423, 426, 440, 736, 752, 809, 843, 851, 857, 867, 1071, 1132, 1152]
  | 13 => [1, 3, 260, 276, 293, 371, 427, 440, 804, 843, 857, 862, 867, 871, 1142, 1178, 1185, 1186]
  | 14 => [1, 3, 260, 277, 293, 371, 428, 440, 827, 843, 857, 867, 870, 871, 1156, 1186]
  | 15 => [1, 3, 260, 292, 293, 371, 440, 843, 857, 860, 867, 875, 1180]
  | 17 => [2, 3, 6, 21, 43, 225, 260, 371, 410, 430, 440, 724, 810, 822, 825, 833, 843, 856, 1086, 1148, 1176]
  | 18 => [2, 3, 6, 21, 43, 234, 260, 371, 413, 430, 440, 689, 802, 810, 825, 833, 843, 856, 1064, 1120, 1129, 1148, 1176]
  | 19 => [2, 3, 6, 21, 43, 244, 260, 371, 430, 440, 782, 810, 833, 843, 853, 856, 1117, 1176]
  | 21 => [2, 3, 6, 21, 225, 260, 282, 371, 410, 440, 724, 810, 822, 825, 837, 843, 851, 856, 1086, 1148]
  | 23 => [2, 3, 6, 21, 244, 260, 282, 371, 440, 782, 810, 837, 843, 851, 853, 856, 1117]
  | 25 => [2, 3, 21, 43, 236, 260, 266, 274, 371, 414, 418, 430, 440, 747, 763, 779, 813, 829, 833, 843, 856, 878, 1093, 1155, 1176]
  | 26 => [2, 3, 21, 43, 236, 260, 266, 371, 414, 418, 430, 440, 747, 763, 779, 813, 829, 833, 843, 856, 1093, 1152, 1155, 1176]
  | 27 => [2, 3, 21, 43, 236, 260, 274, 371, 414, 418, 430, 440, 747, 779, 829, 833, 843, 856, 878, 1093, 1145, 1176]
  | 28 => [2, 3, 21, 43, 236, 260, 371, 414, 418, 430, 440, 747, 779, 829, 833, 843, 856, 1093, 1145, 1152, 1176]
  | 29 => [2, 3, 21, 43, 244, 260, 270, 286, 371, 417, 430, 440, 782, 805, 831, 833, 843, 846, 853, 856, 1117, 1173, 1176]
  | 30 => [2, 3, 21, 43, 244, 260, 270, 371, 417, 430, 440, 782, 831, 833, 843, 853, 856, 1117, 1164, 1176]
  | 34 => [2, 3, 21, 43, 260, 262, 371, 423, 426, 430, 440, 736, 752, 809, 833, 843, 856, 1071, 1132, 1152, 1176]
  | 159 => [3, 6, 13, 21, 43, 159, 215, 220, 254, 260, 371, 387, 396, 440, 602, 616, 653, 706, 725, 769, 784, 810, 833, 843, 856, 869, 990, 1082]
  | 160 => [3, 6, 13, 21, 43, 159, 215, 254, 260, 371, 387, 396, 440, 602, 616, 653, 706, 725, 769, 784, 810, 833, 843, 856, 990, 1078, 1082]
  | 161 => [3, 6, 13, 21, 43, 159, 220, 254, 260, 371, 387, 396, 440, 602, 653, 725, 769, 784, 810, 833, 843, 856, 869, 990, 1073]
  | 162 => [3, 6, 13, 21, 43, 159, 254, 260, 371, 387, 396, 440, 602, 653, 725, 769, 784, 810, 833, 843, 856, 990, 1073, 1078]
  | 163 => [3, 6, 13, 21, 43, 179, 219, 237, 254, 260, 371, 394, 440, 657, 687, 728, 761, 769, 771, 784, 810, 833, 843, 856, 1026, 1114]
  | 164 => [3, 6, 13, 21, 43, 179, 219, 254, 260, 371, 394, 440, 657, 728, 769, 771, 784, 810, 833, 843, 856, 1026, 1105]
  | 168 => [3, 6, 13, 21, 43, 196, 254, 260, 371, 397, 403, 440, 590, 609, 691, 769, 784, 810, 833, 843, 856, 969, 1039, 1078]
  | 195 => [3, 6, 21, 43, 225, 254, 260, 371, 410, 440, 724, 784, 810, 822, 825, 833, 843, 856, 1086, 1148]
  | 196 => [3, 6, 21, 43, 234, 254, 260, 371, 413, 440, 689, 784, 802, 810, 825, 833, 843, 856, 1064, 1120, 1129, 1148]
  | 197 => [3, 6, 21, 43, 244, 254, 260, 371, 440, 782, 784, 810, 833, 843, 853, 856, 1117]
  | 301 => [3, 11, 21, 26, 43, 140, 182, 195, 260, 272, 371, 379, 388, 440, 549, 568, 593, 655, 672, 732, 774, 824, 833, 843, 856, 877, 960, 1050]
  | 302 => [3, 11, 21, 26, 43, 140, 182, 195, 260, 371, 379, 388, 415, 440, 549, 568, 593, 655, 672, 726, 732, 774, 824, 833, 843, 856, 877, 960, 1050, 1150]
  | 303 => [3, 11, 21, 26, 43, 140, 182, 260, 272, 371, 379, 388, 440, 549, 568, 593, 655, 672, 732, 774, 824, 833, 843, 856, 960, 1042, 1050]
  | 304 => [3, 11, 21, 26, 43, 140, 182, 260, 371, 379, 388, 415, 440, 549, 568, 593, 655, 672, 726, 732, 774, 824, 833, 843, 856, 960, 1042, 1050, 1150]
  | 305 => [3, 11, 21, 26, 43, 140, 195, 260, 272, 371, 379, 388, 440, 549, 593, 672, 732, 774, 824, 833, 843, 856, 877, 960, 1029]
  | 306 => [3, 11, 21, 26, 43, 140, 195, 260, 371, 379, 388, 415, 440, 549, 593, 672, 726, 732, 774, 824, 833, 843, 856, 877, 960, 1029, 1150]
  | 307 => [3, 11, 21, 26, 43, 140, 260, 272, 371, 379, 388, 440, 549, 593, 672, 732, 774, 824, 833, 843, 856, 960, 1029, 1042]
  | 308 => [3, 11, 21, 26, 43, 140, 260, 371, 379, 388, 415, 440, 549, 593, 672, 726, 732, 774, 824, 833, 843, 856, 960, 1029, 1042, 1150]
  | 309 => [3, 11, 21, 26, 43, 151, 187, 216, 260, 272, 371, 383, 440, 595, 628, 671, 709, 723, 732, 774, 824, 833, 843, 856, 989, 1085]
  | 310 => [3, 11, 21, 26, 43, 151, 187, 216, 260, 371, 383, 415, 440, 595, 628, 671, 709, 723, 726, 732, 774, 824, 833, 843, 856, 989, 1085, 1150]
  | 311 => [3, 11, 21, 26, 43, 151, 187, 260, 272, 371, 383, 440, 595, 671, 723, 732, 774, 824, 833, 843, 856, 989, 1075]
  | 312 => [3, 11, 21, 26, 43, 151, 187, 260, 371, 383, 415, 440, 595, 671, 723, 726, 732, 774, 824, 833, 843, 856, 989, 1075, 1150]
  | 323 => [3, 11, 21, 26, 43, 203, 260, 272, 371, 401, 405, 440, 539, 555, 643, 732, 774, 824, 833, 843, 856, 947, 1002, 1042]
  | 324 => [3, 11, 21, 26, 43, 203, 260, 371, 401, 405, 415, 440, 539, 555, 643, 726, 732, 774, 824, 833, 843, 856, 947, 1002, 1042, 1150]
  | 325 => [3, 11, 21, 43, 183, 260, 272, 371, 395, 440, 620, 753, 774, 789, 824, 833, 843, 856, 1015, 1088, 1098, 1118]
  | 326 => [3, 11, 21, 43, 183, 260, 371, 395, 415, 440, 620, 726, 753, 774, 789, 824, 833, 843, 856, 1015, 1088, 1098, 1118, 1150]
  | 327 => [3, 11, 21, 43, 197, 260, 272, 371, 398, 440, 666, 774, 786, 789, 824, 833, 843, 856, 1047, 1118]
  | 328 => [3, 11, 21, 43, 197, 260, 371, 398, 415, 440, 666, 726, 774, 786, 789, 824, 833, 843, 856, 1047, 1118, 1150]
  | 329 => [3, 11, 21, 43, 236, 260, 272, 371, 440, 747, 774, 824, 829, 833, 843, 856, 1093]
  | 330 => [3, 11, 21, 43, 236, 260, 371, 415, 440, 726, 747, 774, 824, 829, 833, 843, 856, 1093, 1150]
  | 348 => [3, 20, 21, 42, 43, 130, 166, 175, 249, 260, 371, 373, 381, 440, 445, 524, 532, 554, 612, 642, 795, 806, 824, 833, 843, 856, 946, 1024, 1138, 1150]
  | 349 => [3, 20, 21, 42, 43, 130, 166, 175, 258, 260, 371, 373, 381, 440, 445, 524, 532, 554, 612, 642, 795, 806, 824, 833, 843, 856, 946, 1024, 1150]
  | 350 => [3, 20, 21, 42, 43, 130, 166, 175, 260, 272, 371, 373, 381, 440, 445, 524, 532, 554, 612, 642, 795, 806, 824, 833, 843, 856, 946, 1024]
  | 351 => [3, 20, 21, 42, 43, 130, 166, 175, 260, 371, 373, 381, 421, 440, 445, 524, 532, 554, 612, 642, 692, 795, 806, 824, 833, 843, 856, 946, 1024, 1124, 1138, 1150]
  | 352 => [3, 20, 21, 42, 43, 130, 166, 249, 260, 371, 373, 381, 440, 524, 532, 554, 612, 642, 795, 806, 824, 833, 843, 856, 946, 1013, 1024, 1138, 1150]
  | 353 => [3, 20, 21, 42, 43, 130, 166, 258, 260, 371, 373, 381, 440, 524, 532, 554, 612, 642, 795, 806, 824, 833, 843, 856, 946, 1013, 1024, 1150]
  | 354 => [3, 20, 21, 42, 43, 130, 166, 260, 272, 371, 373, 381, 440, 524, 532, 554, 612, 642, 795, 806, 824, 833, 843, 856, 946, 1013, 1024]
  | 355 => [3, 20, 21, 42, 43, 130, 166, 260, 371, 373, 381, 421, 440, 524, 532, 554, 612, 642, 692, 795, 806, 824, 833, 843, 856, 946, 1013, 1024, 1124, 1138, 1150]
  | 356 => [3, 20, 21, 42, 43, 130, 175, 249, 260, 371, 373, 381, 440, 445, 524, 554, 642, 795, 806, 824, 833, 843, 856, 946, 1003, 1138, 1150]
  | 357 => [3, 20, 21, 42, 43, 130, 175, 258, 260, 371, 373, 381, 440, 445, 524, 554, 642, 795, 806, 824, 833, 843, 856, 946, 1003, 1150]
  | 358 => [3, 20, 21, 42, 43, 130, 175, 260, 272, 371, 373, 381, 440, 445, 524, 554, 642, 795, 806, 824, 833, 843, 856, 946, 1003]
  | 359 => [3, 20, 21, 42, 43, 130, 175, 260, 371, 373, 381, 421, 440, 445, 524, 554, 642, 692, 795, 806, 824, 833, 843, 856, 946, 1003, 1124, 1138, 1150]
  | 360 => [3, 20, 21, 42, 43, 130, 249, 260, 371, 373, 381, 440, 524, 554, 642, 795, 806, 824, 833, 843, 856, 946, 1003, 1013, 1138, 1150]
  | 361 => [3, 20, 21, 42, 43, 130, 258, 260, 371, 373, 381, 440, 524, 554, 642, 795, 806, 824, 833, 843, 856, 946, 1003, 1013, 1150]
  | 362 => [3, 20, 21, 42, 43, 130, 260, 272, 371, 373, 381, 440, 524, 554, 642, 795, 806, 824, 833, 843, 856, 946, 1003, 1013]
  | 363 => [3, 20, 21, 42, 43, 130, 260, 371, 373, 381, 421, 440, 524, 554, 642, 692, 795, 806, 824, 833, 843, 856, 946, 1003, 1013, 1124, 1138, 1150]
  | 364 => [3, 20, 21, 42, 43, 138, 169, 194, 249, 260, 371, 377, 440, 563, 584, 637, 668, 690, 795, 806, 824, 833, 843, 856, 968, 1066, 1138, 1150]
  | 365 => [3, 20, 21, 42, 43, 138, 169, 194, 258, 260, 371, 377, 440, 563, 584, 637, 668, 690, 795, 806, 824, 833, 843, 856, 968, 1066, 1150]
  | 366 => [3, 20, 21, 42, 43, 138, 169, 194, 260, 272, 371, 377, 440, 563, 584, 637, 668, 690, 795, 806, 824, 833, 843, 856, 968, 1066]
  | 367 => [3, 20, 21, 42, 43, 138, 169, 194, 260, 371, 377, 421, 440, 563, 584, 637, 668, 690, 692, 795, 806, 824, 833, 843, 856, 968, 1066, 1124, 1138, 1150]
  | 368 => [3, 20, 21, 42, 43, 138, 169, 249, 260, 371, 377, 440, 563, 637, 690, 795, 806, 824, 833, 843, 856, 968, 1041, 1138, 1150]
  | 369 => [3, 20, 21, 42, 43, 138, 169, 258, 260, 371, 377, 440, 563, 637, 690, 795, 806, 824, 833, 843, 856, 968, 1041, 1150]
  | 370 => [3, 20, 21, 42, 43, 138, 169, 260, 272, 371, 377, 440, 563, 637, 690, 795, 806, 824, 833, 843, 856, 968, 1041]
  | 371 => [3, 20, 21, 42, 43, 138, 169, 260, 371, 377, 421, 440, 563, 637, 690, 692, 795, 806, 824, 833, 843, 856, 968, 1041, 1124, 1138, 1150]
  | 388 => [3, 20, 21, 43, 155, 249, 260, 371, 386, 440, 580, 716, 762, 806, 824, 833, 843, 856, 983, 1068, 1074, 1100, 1138, 1150]
  | 389 => [3, 20, 21, 43, 155, 258, 260, 371, 386, 440, 580, 716, 762, 806, 824, 833, 843, 856, 983, 1068, 1074, 1100, 1150]
  | 390 => [3, 20, 21, 43, 155, 260, 272, 371, 386, 440, 580, 716, 762, 806, 824, 833, 843, 856, 983, 1068, 1074, 1100]
  | 391 => [3, 20, 21, 43, 155, 260, 371, 386, 421, 440, 580, 692, 716, 762, 806, 824, 833, 843, 856, 983, 1068, 1074, 1100, 1124, 1138, 1150]
  | 392 => [3, 20, 21, 43, 173, 249, 260, 371, 390, 440, 634, 755, 762, 806, 824, 833, 843, 856, 1019, 1100, 1138, 1150]
  | 393 => [3, 20, 21, 43, 173, 258, 260, 371, 390, 440, 634, 755, 762, 806, 824, 833, 843, 856, 1019, 1100, 1150]
  | 394 => [3, 20, 21, 43, 173, 260, 272, 371, 390, 440, 634, 755, 762, 806, 824, 833, 843, 856, 1019, 1100]
  | 395 => [3, 20, 21, 43, 173, 260, 371, 390, 421, 440, 634, 692, 755, 762, 806, 824, 833, 843, 856, 1019, 1100, 1124, 1138, 1150]
  | 400 => [3, 20, 21, 43, 249, 260, 262, 371, 440, 736, 806, 809, 824, 833, 843, 856, 1071, 1138, 1150]
  | 401 => [3, 20, 21, 43, 258, 260, 262, 371, 440, 736, 806, 809, 824, 833, 843, 856, 1071, 1150]
  | 402 => [3, 20, 21, 43, 260, 262, 272, 371, 440, 736, 806, 809, 824, 833, 843, 856, 1071]
  | 403 => [3, 20, 21, 43, 260, 262, 371, 421, 440, 692, 736, 806, 809, 824, 833, 843, 856, 1071, 1124, 1138, 1150]
  | 404 => [3, 21, 43, 236, 252, 260, 266, 272, 371, 414, 440, 747, 763, 779, 813, 824, 829, 833, 843, 856, 1093, 1155]
  | 405 => [3, 21, 43, 236, 252, 260, 266, 371, 414, 415, 440, 726, 747, 763, 779, 813, 824, 829, 833, 843, 856, 1093, 1150, 1155]
  | 406 => [3, 21, 43, 236, 252, 260, 272, 371, 414, 440, 747, 779, 824, 829, 833, 843, 856, 1093, 1145]
  | 407 => [3, 21, 43, 236, 252, 260, 371, 414, 415, 440, 726, 747, 779, 824, 829, 833, 843, 856, 1093, 1145, 1150]
  | 408 => [3, 21, 43, 244, 254, 260, 270, 286, 371, 417, 440, 782, 784, 805, 831, 833, 843, 846, 853, 856, 1117, 1173]
  | 409 => [3, 21, 43, 244, 254, 260, 270, 371, 417, 440, 782, 784, 831, 833, 843, 853, 856, 1117, 1164]
  | 411 => [3, 21, 43, 249, 260, 262, 263, 371, 423, 440, 736, 752, 809, 824, 833, 843, 856, 1071, 1132, 1138, 1150]
  | 418 => [3, 21, 43, 258, 260, 262, 263, 371, 423, 440, 736, 752, 809, 824, 833, 843, 856, 1071, 1132, 1150]
  | 419 => [3, 21, 43, 260, 262, 263, 272, 371, 423, 440, 736, 752, 809, 824, 833, 843, 856, 1071, 1132]
  | 420 => [3, 21, 43, 260, 262, 263, 371, 421, 423, 440, 692, 736, 752, 809, 824, 833, 843, 856, 1071, 1124, 1132, 1138, 1150]
  | 494 => [3, 21, 260, 275, 276, 371, 440, 442, 804, 843, 856, 862, 1142]
  | 514 => [3, 21, 260, 282, 292, 371, 440, 837, 843, 856, 860, 875, 1180]
  | 515 => [3, 260, 292, 293, 297, 298, 371, 438, 440, 843, 857, 860, 864, 872, 874, 875, 1180, 1188]
  | 516 => [3, 260, 292, 293, 297, 371, 438, 440, 843, 857, 860, 872, 875, 1180, 1187]
  | _ => []
private def src96 : List (List Nat) := [[371,843,260,440,3,293,857,867,1,851,2,1152,426,752,1132,423,736,809,1071,262]]
private def recs96 : List LowerHistoryRecord := [⟨.left,96,0,(-1),false,10,225⟩]
private theorem check96 : recs96.all (recordCheck path96 src96 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path96_binding : lowerHistoryPathBinding path96 := by
  apply pathBinding_from_ids path96 src96 [] recs96 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source96 rfl records96 rfl
  · intro r hr _
    simp only [recs96, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise10)
  · intro r hr _
    simp only [recs96, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path96] using WitnessLookup16.witness225_projection
  · exact check96
  · exact BatchCoverage15.coverage_sound path96 recs96
      records96 SourceValues16.length96 BatchCoverageAll16.coverage96
private def src97 : List (List Nat) := [[371,843,260,440,3,293,857,867,1,851,2,1152,418,779,1145,414,747,829,1093,236],[371,843,260,440,3,293,857,867,1,851,2,1152,418,779,266,813,763,1155,414,747,829,1093,236],[371,843,260,440,3,293,857,867,1,851,2,274,878,418,779,1145,414,747,829,1093,236],[371,843,260,440,3,293,857,867,1,851,2,274,878,418,779,266,813,763,1155,414,747,829,1093,236]]
private def recs97 : List LowerHistoryRecord := [⟨.left,97,0,(-1),false,4,231⟩,⟨.left,97,1,(-1),false,2,231⟩,⟨.left,97,2,(-1),false,3,231⟩,⟨.left,97,3,(-1),false,1,231⟩]
private theorem check97 : recs97.all (recordCheck path97 src97 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path97_binding : lowerHistoryPathBinding path97 := by
  apply pathBinding_from_ids path97 src97 [] recs97 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source97 rfl records97 rfl
  · intro r hr _
    simp only [recs97, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise4)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise2)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise3)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise1)
  · intro r hr _
    simp only [recs97, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [wids, path97] using WitnessLookup16.witness231_projection
    · simpa only [wids, path97] using WitnessLookup16.witness231_projection
    · simpa only [wids, path97] using WitnessLookup16.witness231_projection
    · simpa only [wids, path97] using WitnessLookup16.witness231_projection
  · exact check97
  · exact BatchCoverage15.coverage_sound path97 recs97
      records97 SourceValues16.length97 BatchCoverageAll16.coverage97
private def src98 : List (List Nat) := [[371,843,260,440,3,293,857,867,1,851,2,270,831,1164,417,782,853,1117,244],[371,843,260,440,3,293,857,867,1,851,2,270,831,286,846,805,1173,417,782,853,1117,244]]
private def recs98 : List LowerHistoryRecord := [⟨.left,98,0,(-1),false,6,237⟩,⟨.left,98,1,(-1),false,5,237⟩]
private theorem check98 : recs98.all (recordCheck path98 src98 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path98_binding : lowerHistoryPathBinding path98 := by
  apply pathBinding_from_ids path98 src98 [] recs98 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source98 rfl records98 rfl
  · intro r hr _
    simp only [recs98, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise6)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise5)
  · intro r hr _
    simp only [recs98, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [wids, path98] using WitnessLookup16.witness237_projection
    · simpa only [wids, path98] using WitnessLookup16.witness237_projection
  · exact check98
  · exact BatchCoverage15.coverage_sound path98 recs98
      records98 SourceValues16.length98 BatchCoverageAll16.coverage98
private def src99 : List (List Nat) := [[371,843,260,440,3,293,857,297,872,1187,438,860,875,1180,292],[371,843,260,440,3,293,857,297,872,298,874,864,1188,438,860,875,1180,292]]
private def recs99 : List LowerHistoryRecord := [⟨.left,99,0,(-1),false,516,290⟩,⟨.left,99,1,(-1),false,515,296⟩]
private theorem check99 : recs99.all (recordCheck path99 src99 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path99_binding : lowerHistoryPathBinding path99 := by
  apply pathBinding_from_ids path99 src99 [] recs99 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source99 rfl records99 rfl
  · intro r hr _
    simp only [recs99, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise516)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise515)
  · intro r hr _
    simp only [recs99, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [wids, path99] using WitnessLookup16.witness290_projection
    · simpa only [wids, path99] using WitnessLookup16.witness296_projection
  · exact check99
  · exact BatchCoverage15.coverage_sound path99 recs99
      records99 SourceValues16.length99 BatchCoverageAll16.coverage99
private def src100 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,276,804,862,1142]]
private def recs100 : List LowerHistoryRecord := [⟨.left,100,0,(-1),false,494,1185⟩]
private theorem check100 : recs100.all (recordCheck path100 src100 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path100_binding : lowerHistoryPathBinding path100 := by
  apply pathBinding_from_ids path100 src100 [] recs100 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source100 rfl records100 rfl
  · intro r hr _
    simp only [recs100, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise494)
  · intro r hr _
    simp only [recs100, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path100] using WitnessLookup16.witness1185_projection
  · exact check100
  · exact BatchCoverage15.coverage_sound path100 recs100
      records100 SourceValues16.length100 BatchCoverageAll16.coverage100
end BatchIdSolution50
theorem _root_.solution : lowerHistoryBindingBatch 95 100 := by
  intro i hlo hhi p hp
  interval_cases i
  · have he := Option.some.inj (PathLookup16.path96_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path96_binding
  · have he := Option.some.inj (PathLookup16.path97_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path97_binding
  · have he := Option.some.inj (PathLookup16.path98_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path98_binding
  · have he := Option.some.inj (PathLookup16.path99_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path99_binding
  · have he := Option.some.inj (PathLookup16.path100_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path100_binding
end M7Binding50Sep15
#print axioms solution
