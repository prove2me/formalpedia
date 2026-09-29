-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0000_0005
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T17:52:08.36282+00:00
-- url     : https://prove2.me/submissions/74273019-5d58-4c6c-8d2a-304c9e546709

import Definitions.Def_Freiman_lowerHistoryVerification
import Mathlib.Tactic
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
private theorem norm1 : lowerHistoryNormalization ([2,3],[3,1]) true false = ⟨true,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm2 : lowerHistoryNormalization ([2,3],[3,1]) false false = ⟨false,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm3 : lowerHistoryNormalization ([2,3,3],[3,1]) true true = ⟨true,true,⟨⟨(7863/213110),0,0,(287/213110)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(921/2110),0,0,(-1/2110)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm4 : lowerHistoryNormalization ([2,3,3,1],[3,1]) true true = ⟨true,true,⟨⟨(2153/92819),0,0,(-114/92819)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(799/1838),0,0,(-1/5514)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm5 : lowerHistoryNormalization ([2,3,2],[3,1]) true true = ⟨true,true,⟨⟨(4341/86941),0,0,(560/86941)⟩,⟨(193/454),0,0,(1/454)⟩,⟨(339/766),0,0,(-1/766)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm6 : lowerHistoryNormalization ([2,3,2,1],[3,1]) true true = ⟨true,true,⟨⟨(14073/609722),0,0,(1115/609722)⟩,⟨(193/454),0,0,(1/454)⟩,⟨(1175/2686),0,0,(-1/2686)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm7 : lowerHistoryNormalization ([2,3,1],[3,1]) true false = ⟨true,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm8 : lowerHistoryNormalization ([2,3,1,1],[3,1]) true true = ⟨true,true,⟨⟨(1607/35615),0,0,(208/35615)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(373/838),0,0,(-1/838)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm9 : lowerHistoryNormalization ([2,3,1],[3,1]) false false = ⟨false,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm10 : lowerHistoryNormalization ([2,3,1,2],[3,1]) true true = ⟨true,true,⟨⟨(5149/218578),0,0,(533/218578)⟩,⟨(327/746),0,0,(1/2238)⟩,⟨(263/586),0,0,(-1/586)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey0 : lowerHistoryPull (lowerHistoryH7) ([2],[3]) false = ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey1 : lowerHistoryPull (lowerHistoryH9) ([2],[3]) false = ⟨false,false,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey2 : lowerHistoryPull (lowerHistoryH7) ([2,3],[3,1]) true = ⟨false,false,⟨⟨(180467950/78144583),(-151370050/234433749),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey3 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,3],[3,1]) true = ⟨false,true,⟨⟨(228931/687489),(44448/229163),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey4 : lowerHistoryPull (lowerHistoryHN) ([2,3],[3,1]) true = ⟨true,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey5 : lowerHistoryPull (lowerHistoryH7) ([2,3],[3,1]) false = ⟨true,false,⟨⟨(10794293/86578700),(1930959/86578700),0,0⟩,⟨(529/1222),(1/1222),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey6 : lowerHistoryPull (lowerHistoryH2) ([2,3,3],[3,1]) true = ⟨false,true,⟨⟨(38176617350/719752746817),(770747150/2159258240451),0,0⟩,⟨(8265/19058),(-1/57174),0,0⟩,⟨(68128/157033),(1/157033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey7 : lowerHistoryPull (lowerHistoryH7) ([2,3,3,1],[3,1]) true = ⟨false,false,⟨⟨(2410328050/27532408541),(-2062338200/82597225623),0,0⟩,⟨(7696/17749),(1/17749),0,0⟩,⟨(3947/9098),(-1/27294),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey8 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,3,3,1],[3,1]) true = ⟨false,true,⟨⟨(5999083/484441206),(3495047/484441206),0,0⟩,⟨(7696/17749),(1/17749),0,0⟩,⟨(3947/9098),(-1/27294),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey9 : lowerHistoryPull (lowerHistoryHN) ([2,3,3,1],[3,1]) true = ⟨true,false,⟨⟨(2153/92819),0,0,(-114/92819)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(799/1838),0,0,(-1/5514)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey10 : lowerHistoryPull (lowerHistoryH9) ([2,3],[3,1]) false = ⟨false,false,⟨⟨(45303/35893),(-58924/107679),0,0⟩,⟨(9/22),(1/66),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey11 : lowerHistoryPull (lowerHistoryH2) ([2,3,2],[3,1]) true = ⟨false,true,⟨⟨(551966364900/5786984313539),(9947987200/17360952940617),0,0⟩,⟨(13997/32149),(-1/32149),0,0⟩,⟨(12542/28787),(1/86361),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey12 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,3,2],[3,1]) true = ⟨false,false,⟨⟨(757714257500/6143085145791),(40506921500/18429255437373),0,0⟩,⟨(12542/28787),(1/86361),0,0⟩,⟨(1865/4273),(-1/4273),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey13 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,3,2],[3,1]) true = ⟨false,false,⟨⟨(63791723/1577072636),(30420835/788536318),0,0⟩,⟨(2455/5638),(1/5638),0,0⟩,⟨(61047/139861),(-1/139861),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey14 : lowerHistoryPull (lowerHistoryH23) ([2,3,2],[3,1]) true = ⟨false,true,⟨⟨(210400854500/1526263336169),(-10382610500/1526263336169),0,0⟩,⟨(12542/28787),(1/86361),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey15 : lowerHistoryPull (lowerHistoryH7) ([2,3,2,1],[3,1]) true = ⟨false,false,⟨⟨(2693208050/17223665503),(-2296763950/51670996509),0,0⟩,⟨(1462/3359),(1/10077),0,0⟩,⟨(6551/15037),(-1/15037),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey16 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,3,2,1],[3,1]) true = ⟨false,true,⟨⟨(3362449/151527849),(1958876/151527849),0,0⟩,⟨(1462/3359),(1/10077),0,0⟩,⟨(6551/15037),(-1/15037),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey17 : lowerHistoryPull (lowerHistoryHN) ([2,3,2,1],[3,1]) true = ⟨true,false,⟨⟨(14073/609722),0,0,(1115/609722)⟩,⟨(193/454),0,0,(1/454)⟩,⟨(1175/2686),0,0,(-1/2686)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey18 : lowerHistoryPull (lowerHistoryH2) ([2,3,1],[3,1]) true = ⟨false,true,⟨⟨(359490461150/1636553162387),(1650599750/1636553162387),0,0⟩,⟨(6265/14278),(-1/14278),0,0⟩,⟨(16112/36661),(1/36661),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey19 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,3,1],[3,1]) true = ⟨false,false,⟨⟨(453773786500/1470202261803),(-2455000/1470202261803),0,0⟩,⟨(16112/36661),(1/36661),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey20 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,3,1],[3,1]) true = ⟨false,false,⟨⟨(4474391/43366226),(25043537/260197356),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(23151/52438),(-1/52438),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey21 : lowerHistoryPull (lowerHistoryH23) ([2,3,1],[3,1]) true = ⟨false,true,⟨⟨(263287960500/786278842063),(-21629154500/786278842063),0,0⟩,⟨(16112/36661),(1/36661),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey22 : lowerHistoryPull (lowerHistoryH7) ([2,3,1,1],[3,1]) true = ⟨false,false,⟨⟨(1770570100/4981629103),(-500309550/4981629103),0,0⟩,⟨(2000/4561),(1/4561),0,0⟩,⟨(2815/6406),(-1/6406),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey23 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,3,1,1],[3,1]) true = ⟨false,true,⟨⟨(1482277/29217766),(2590429/87653298),0,0⟩,⟨(2000/4561),(1/4561),0,0⟩,⟨(2815/6406),(-1/6406),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey24 : lowerHistoryPull (lowerHistoryHN) ([2,3,1,1],[3,1]) true = ⟨true,false,⟨⟨(1607/35615),0,0,(208/35615)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(373/838),0,0,(-1/838)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey25 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) false = ⟨false,false,⟨⟨(1208864407/7105666700),(-9395003/10658500050),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey26 : lowerHistoryPull (lowerHistoryH5) ([2,3,1],[3,1]) false = ⟨false,true,⟨⟨(10372299021/84769894000),(-28232289/84769894000),0,0⟩,⟨(31755/72022),(1/72022),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey27 : lowerHistoryPull (lowerHistoryH7) ([2,3,1,2],[3,1]) true = ⟨false,false,⟨⟨(334320350/1963632473),(-93705300/1963632473),0,0⟩,⟨(4407/10006),(1/10006),0,0⟩,⟨(5582/12661),(-1/12661),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey28 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,3,1,2],[3,1]) true = ⟨false,true,⟨⟨(3102727/126685966),(5421829/380057898),0,0⟩,⟨(4407/10006),(1/10006),0,0⟩,⟨(5582/12661),(-1/12661),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey29 : lowerHistoryPull (lowerHistoryHN) ([2,3,1,2],[3,1]) true = ⟨true,false,⟨⟨(5149/218578),0,0,(533/218578)⟩,⟨(327/746),0,0,(1/2238)⟩,⟨(263/586),0,0,(-1/586)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pull1 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = ⟨true,true,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey1]
  rfl
private theorem pull5 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH7) ([2,3],[3,1]) false = ⟨false,true,⟨⟨(10794293/86578700),(1930959/86578700),0,0⟩,⟨(529/1222),(1/1222),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey5]
  rfl
private theorem pull13 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,3,2],[3,1]) true = ⟨true,false,⟨⟨(551966364900/5786984313539),(9947987200/17360952940617),0,0⟩,⟨(13997/32149),(-1/32149),0,0⟩,⟨(12542/28787),(1/86361),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey11]
  rfl
private theorem pull21 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) true = ⟨true,false,⟨⟨(359490461150/1636553162387),(1650599750/1636553162387),0,0⟩,⟨(6265/14278),(-1/14278),0,0⟩,⟨(16112/36661),(1/36661),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey18]
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
namespace BindingOps20_1
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b21 : CertBound) (b260 : CertBound) (b275 : CertBound) (b276 : CertBound) (b371 : CertBound) (b440 : CertBound) (b442 : CertBound) (b804 : CertBound) (b843 : CertBound) (b856 : CertBound) (b862 : CertBound) (b1142 : CertBound)
private def path : LowerHistoryPath := ⟨.left,1,[1],([2],[3]),false,[(([3],[1]),true)],([1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[1]),true)⟩ ([2,3],[3,1]) = some [b804])
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
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([3],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hdone, hchoice0, hdone0, hforced0, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps20_1
namespace BindingOps20_2
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b7 : CertBound) (b21 : CertBound) (b177 : CertBound) (b260 : CertBound) (b275 : CertBound) (b371 : CertBound) (b392 : CertBound) (b399 : CertBound) (b440 : CertBound) (b442 : CertBound) (b627 : CertBound) (b650 : CertBound) (b718 : CertBound) (b814 : CertBound) (b843 : CertBound) (b856 : CertBound) (b984 : CertBound) (b1067 : CertBound) (b1107 : CertBound)
private def path : LowerHistoryPath := ⟨.left,2,[1],([2],[3]),false,[(([3],[1]),false),(([3],[]),true),(([],[1]),false)],([1,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [b7])
    (hb2 : ops.necessary ⟨⟨([1,2,3,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,3,3],[3,1]) = some [b650])
    (hb3 : ops.necessary ⟨⟨([1,2,3,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,3,1],[3,1]) = some [b627])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,3],[3,1]) false false = b814)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,3],[3,1]) false = b1107)
    (hn5 : ops.normalization ([2,3,3],[3,1]) true true = b399)
    (hn6 : ops.pull (lowerHistoryH2) ([2,3,3],[3,1]) true = b1067)
    (hn7 : ops.normalization ([2,3,3,1],[3,1]) true true = b392)
    (hn8 : ops.pull (lowerHistoryH7) ([2,3,3,1],[3,1]) true = b718)
    (hn9 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,3,3,1],[3,1]) true = b984)
    (hn10 : ops.pull (lowerHistoryHN) ([2,3,3,1],[3,1]) true = b177)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b399,b650,b1067,b392,b627,b718,b984,b177].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b399,b650,b1067,b392,b627,b718,b984,b177]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b399,b650,b1067,b392,b627,b718,b984,b177]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([3],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH7]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,3,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps20_2
namespace BindingOps20_3
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b7 : CertBound) (b21 : CertBound) (b176 : CertBound) (b230 : CertBound) (b239 : CertBound) (b260 : CertBound) (b275 : CertBound) (b371 : CertBound) (b391 : CertBound) (b406 : CertBound) (b440 : CertBound) (b442 : CertBound) (b646 : CertBound) (b658 : CertBound) (b697 : CertBound) (b740 : CertBound) (b754 : CertBound) (b814 : CertBound) (b843 : CertBound) (b850 : CertBound) (b856 : CertBound) (b1016 : CertBound) (b1094 : CertBound) (b1107 : CertBound) (b1111 : CertBound)
private def path : LowerHistoryPath := ⟨.left,3,[1],([2],[3]),false,[(([3],[1]),false),(([2],[]),true),(([],[1]),false)],([1,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [b7])
    (hb2 : ops.necessary ⟨⟨([1,2,3,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,3,2],[3,1]) = some [b697])
    (hb3 : ops.necessary ⟨⟨([1,2,3,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,2,1],[3,1]) = some [b646])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,3],[3,1]) false false = b814)
    (hn4 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,3],[3,1]) false = b1107)
    (hn5 : ops.pull (lowerHistoryH7) ([2,3],[3,1]) false = b239)
    (hn6 : ops.pull (lowerHistoryH9) ([2,3],[3,1]) false = b850)
    (hn7 : ops.normalization ([2,3,2],[3,1]) true true = b406)
    (hn8 : ops.pull (lowerHistoryH2) ([2,3,2],[3,1]) true = b1094)
    (hn9 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,3,2],[3,1]) true = b230)
    (hn10 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,3,2],[3,1]) true = b740)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,3,2],[3,1]) true = b658)
    (hn12 : ops.pull (lowerHistoryH23) ([2,3,2],[3,1]) true = b1111)
    (hn13 : ops.normalization ([2,3,2,1],[3,1]) true true = b391)
    (hn14 : ops.pull (lowerHistoryH7) ([2,3,2,1],[3,1]) true = b754)
    (hn15 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,3,2,1],[3,1]) true = b1016)
    (hn16 : ops.pull (lowerHistoryHN) ([2,3,2,1],[3,1]) true = b176)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b1094,b391,b646,b754,b1016,b176].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176]
] : List (List CertBound))[1])
    (herase2 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b1094,b391,b646,b754,b1016,b176].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176]
] : List (List CertBound))[2])
    (herase3 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176]
] : List (List CertBound))[3])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b1107,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b1094,b391,b646,b754,b1016,b176],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b239,b850,b406,b697,b230,b740,b658,b1111,b391,b646,b754,b1016,b176]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([3],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,3,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1, herase2, herase3]
  rfl
end BindingOps20_3
namespace BindingOps20_4
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b7 : CertBound) (b21 : CertBound) (b207 : CertBound) (b251 : CertBound) (b260 : CertBound) (b264 : CertBound) (b275 : CertBound) (b371 : CertBound) (b404 : CertBound) (b440 : CertBound) (b442 : CertBound) (b699 : CertBound) (b729 : CertBound) (b788 : CertBound) (b793 : CertBound) (b803 : CertBound) (b814 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1065 : CertBound) (b1126 : CertBound) (b1143 : CertBound)
private def path : LowerHistoryPath := ⟨.left,4,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),true),(([],[1]),false)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [b7])
    (hb2 : ops.necessary ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,3,1],[3,1]) = some [b788])
    (hb3 : ops.necessary ⟨⟨([1,2,3,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,3,1,1],[3,1]) = some [b699])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,3],[3,1]) false false = b814)
    (hn4 : ops.normalization ([2,3,1],[3,1]) true false = b264)
    (hn5 : ops.pull (lowerHistoryH2) ([2,3,1],[3,1]) true = b1126)
    (hn6 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) true = b251)
    (hn7 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,3,1],[3,1]) true = b793)
    (hn8 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,3,1],[3,1]) true = b729)
    (hn9 : ops.pull (lowerHistoryH23) ([2,3,1],[3,1]) true = b1143)
    (hn10 : ops.normalization ([2,3,1,1],[3,1]) true true = b404)
    (hn11 : ops.pull (lowerHistoryH7) ([2,3,1,1],[3,1]) true = b803)
    (hn12 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,3,1,1],[3,1]) true = b1065)
    (hn13 : ops.pull (lowerHistoryHN) ([2,3,1,1],[3,1]) true = b207)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b264,b788,b1126,b404,b699,b803,b1065,b207].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b264,b788,b1126,b404,b699,b803,b1065,b207],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b264,b788,b251,b793,b729,b1143,b404,b699,b803,b1065,b207]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b264,b788,b251,b793,b729,b1143,b404,b699,b803,b1065,b207].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b264,b788,b1126,b404,b699,b803,b1065,b207],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b264,b788,b251,b793,b729,b1143,b404,b699,b803,b1065,b207]
] : List (List CertBound))[1])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b264,b788,b1126,b404,b699,b803,b1065,b207],
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b264,b788,b251,b793,b729,b1143,b404,b699,b803,b1065,b207]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([3],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1]
  rfl
end BindingOps20_4
namespace BindingOps20_5
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b7 : CertBound) (b19 : CertBound) (b21 : CertBound) (b178 : CertBound) (b260 : CertBound) (b275 : CertBound) (b371 : CertBound) (b393 : CertBound) (b440 : CertBound) (b442 : CertBound) (b621 : CertBound) (b766 : CertBound) (b767 : CertBound) (b807 : CertBound) (b814 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1022 : CertBound) (b1106 : CertBound)
private def path : LowerHistoryPath := ⟨.left,5,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([2,3],[3,1]) = some [b7])
    (hb2 : ops.necessary ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,3,1],[3,1]) = some [b19])
    (hb3 : ops.necessary ⟨⟨([1,2,3,1,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,3,1,2],[3,1]) = some [b621])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.pull (lowerHistoryH7) ([2],[3]) false = b275)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2],[3]) false = b442)
    (hn3 : ops.normalization ([2,3],[3,1]) false false = b814)
    (hn4 : ops.normalization ([2,3,1],[3,1]) false false = b807)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,3,1],[3,1]) false = b766)
    (hn6 : ops.pull (lowerHistoryH5) ([2,3,1],[3,1]) false = b1106)
    (hn7 : ops.normalization ([2,3,1,2],[3,1]) true true = b393)
    (hn8 : ops.pull (lowerHistoryH7) ([2,3,1,2],[3,1]) true = b767)
    (hn9 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,3,1,2],[3,1]) true = b1022)
    (hn10 : ops.pull (lowerHistoryHN) ([2,3,1,2],[3,1]) true = b178)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b807,b19,b766,b1106,b393,b621,b767,b1022,b178].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b807,b19,b766,b1106,b393,b621,b767,b1022,b178]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b275,b442,b814,b7,b807,b19,b766,b1106,b393,b621,b767,b1022,b178]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([3],[1]) = [[lowerHistoryH7,lowerHistoryComplement lowerHistoryH9]] := by rfl
  have hdone0 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced0 : decide (([3],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,3],[3,1,3,1]),(false,false)⟩,false,true,some (false,([3],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,3,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps20_5

open Freiman

private abbrev sourceBound3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩

private abbrev sourceBound7 : CertBound := ⟨true,false,⟨⟨(-2415463/5270749),(1816717/5270749),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private abbrev sourceBound19 : CertBound := ⟨true,false,⟨⟨(-2957543/15273863),(2209052/15273863),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private abbrev sourceBound21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private abbrev sourceBound176 : CertBound := ⟨true,false,⟨⟨(14073/609722),0,0,(1115/609722)⟩,⟨(193/454),0,0,(1/454)⟩,⟨(1175/2686),0,0,(-1/2686)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound177 : CertBound := ⟨true,false,⟨⟨(2153/92819),0,0,(-114/92819)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(799/1838),0,0,(-1/5514)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound178 : CertBound := ⟨true,false,⟨⟨(5149/218578),0,0,(533/218578)⟩,⟨(327/746),0,0,(1/2238)⟩,⟨(263/586),0,0,(-1/586)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound207 : CertBound := ⟨true,false,⟨⟨(1607/35615),0,0,(208/35615)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(373/838),0,0,(-1/838)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound230 : CertBound := ⟨true,false,⟨⟨(551966364900/5786984313539),(9947987200/17360952940617),0,0⟩,⟨(13997/32149),(-1/32149),0,0⟩,⟨(12542/28787),(1/86361),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound239 : CertBound := ⟨true,false,⟨⟨(10794293/86578700),(1930959/86578700),0,0⟩,⟨(529/1222),(1/1222),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound251 : CertBound := ⟨true,false,⟨⟨(359490461150/1636553162387),(1650599750/1636553162387),0,0⟩,⟨(6265/14278),(-1/14278),0,0⟩,⟨(16112/36661),(1/36661),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound260 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private abbrev sourceBound264 : CertBound := ⟨true,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound275 : CertBound := ⟨true,false,⟨⟨(3087972/5986825),(290501/2394730),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound276 : CertBound := ⟨true,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound371 : CertBound := ⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

private abbrev sourceBound391 : CertBound := ⟨true,true,⟨⟨(14073/609722),0,0,(1115/609722)⟩,⟨(193/454),0,0,(1/454)⟩,⟨(1175/2686),0,0,(-1/2686)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound392 : CertBound := ⟨true,true,⟨⟨(2153/92819),0,0,(-114/92819)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(799/1838),0,0,(-1/5514)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound393 : CertBound := ⟨true,true,⟨⟨(5149/218578),0,0,(533/218578)⟩,⟨(327/746),0,0,(1/2238)⟩,⟨(263/586),0,0,(-1/586)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound399 : CertBound := ⟨true,true,⟨⟨(7863/213110),0,0,(287/213110)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(921/2110),0,0,(-1/2110)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound404 : CertBound := ⟨true,true,⟨⟨(1607/35615),0,0,(208/35615)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(373/838),0,0,(-1/838)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound406 : CertBound := ⟨true,true,⟨⟨(4341/86941),0,0,(560/86941)⟩,⟨(193/454),0,0,(1/454)⟩,⟨(339/766),0,0,(-1/766)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private abbrev sourceBound442 : CertBound := ⟨true,true,⟨⟨(3317/299),(-1683/299),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨1,(-1/3),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private abbrev sourceBound621 : CertBound := ⟨false,false,⟨⟨(41681/1638923),(357512/4916769),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound627 : CertBound := ⟨false,false,⟨⟨(2496968/95947501),(5603863/287842503),0,0⟩,⟨(8265/19058),(-1/57174),0,0⟩,⟨(4367/10069),(1/10069),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound646 : CertBound := ⟨false,false,⟨⟨(2664700/82712279),(5005419/82712279),0,0⟩,⟨(2455/5638),(1/5638),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound650 : CertBound := ⟨false,false,⟨⟨(15846/447863),(105176/1343589),0,0⟩,⟨(529/1222),(1/1222),0,0⟩,⟨(8265/19058),(-1/57174),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound658 : CertBound := ⟨false,false,⟨⟨(63791723/1577072636),(30420835/788536318),0,0⟩,⟨(2455/5638),(1/5638),0,0⟩,⟨(61047/139861),(-1/139861),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound697 : CertBound := ⟨false,false,⟨⟨(482605/7364591),(3580367/22093773),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound699 : CertBound := ⟨false,false,⟨⟨(661229/9815663),(4179215/29446989),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound718 : CertBound := ⟨false,false,⟨⟨(2410328050/27532408541),(-2062338200/82597225623),0,0⟩,⟨(7696/17749),(1/17749),0,0⟩,⟨(3947/9098),(-1/27294),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound729 : CertBound := ⟨false,false,⟨⟨(4474391/43366226),(25043537/260197356),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(23151/52438),(-1/52438),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound740 : CertBound := ⟨false,false,⟨⟨(757714257500/6143085145791),(40506921500/18429255437373),0,0⟩,⟨(12542/28787),(1/86361),0,0⟩,⟨(1865/4273),(-1/4273),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private abbrev sourceBound754 : CertBound := ⟨false,false,⟨⟨(2693208050/17223665503),(-2296763950/51670996509),0,0⟩,⟨(1462/3359),(1/10077),0,0⟩,⟨(6551/15037),(-1/15037),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound766 : CertBound := ⟨false,false,⟨⟨(1208864407/7105666700),(-9395003/10658500050),0,0⟩,⟨(363/827),(1/2481),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩

private abbrev sourceBound767 : CertBound := ⟨false,false,⟨⟨(334320350/1963632473),(-93705300/1963632473),0,0⟩,⟨(4407/10006),(1/10006),0,0⟩,⟨(5582/12661),(-1/12661),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound788 : CertBound := ⟨false,false,⟨⟨(534009/1863433),(1199347/5590299),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound793 : CertBound := ⟨false,false,⟨⟨(453773786500/1470202261803),(-2455000/1470202261803),0,0⟩,⟨(16112/36661),(1/36661),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private abbrev sourceBound803 : CertBound := ⟨false,false,⟨⟨(1770570100/4981629103),(-500309550/4981629103),0,0⟩,⟨(2000/4561),(1/4561),0,0⟩,⟨(2815/6406),(-1/6406),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound804 : CertBound := ⟨false,false,⟨⟨(911720/2447159),(6369548/7341477),0,0⟩,⟨(761/1727),(1/5181),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound807 : CertBound := ⟨false,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(73/170),0,0,(1/510)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound814 : CertBound := ⟨false,false,⟨⟨(537/1010),0,0,(-13/1010)⟩,⟨(83/202),0,0,(1/202)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private abbrev sourceBound843 : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩

private abbrev sourceBound850 : CertBound := ⟨false,false,⟨⟨(45303/35893),(-58924/107679),0,0⟩,⟨(9/22),(1/66),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound856 : CertBound := ⟨false,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private abbrev sourceBound862 : CertBound := ⟨false,false,⟨⟨(180467950/78144583),(-151370050/234433749),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private abbrev sourceBound984 : CertBound := ⟨false,true,⟨⟨(5999083/484441206),(3495047/484441206),0,0⟩,⟨(7696/17749),(1/17749),0,0⟩,⟨(3947/9098),(-1/27294),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1016 : CertBound := ⟨false,true,⟨⟨(3362449/151527849),(1958876/151527849),0,0⟩,⟨(1462/3359),(1/10077),0,0⟩,⟨(6551/15037),(-1/15037),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1022 : CertBound := ⟨false,true,⟨⟨(3102727/126685966),(5421829/380057898),0,0⟩,⟨(4407/10006),(1/10006),0,0⟩,⟨(5582/12661),(-1/12661),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1065 : CertBound := ⟨false,true,⟨⟨(1482277/29217766),(2590429/87653298),0,0⟩,⟨(2000/4561),(1/4561),0,0⟩,⟨(2815/6406),(-1/6406),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1067 : CertBound := ⟨false,true,⟨⟨(38176617350/719752746817),(770747150/2159258240451),0,0⟩,⟨(8265/19058),(-1/57174),0,0⟩,⟨(68128/157033),(1/157033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1094 : CertBound := ⟨false,true,⟨⟨(551966364900/5786984313539),(9947987200/17360952940617),0,0⟩,⟨(13997/32149),(-1/32149),0,0⟩,⟨(12542/28787),(1/86361),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1106 : CertBound := ⟨false,true,⟨⟨(10372299021/84769894000),(-28232289/84769894000),0,0⟩,⟨(31755/72022),(1/72022),0,0⟩,⟨(709/1606),(-1/1606),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

private abbrev sourceBound1107 : CertBound := ⟨false,true,⟨⟨(10794293/86578700),(1930959/86578700),0,0⟩,⟨(529/1222),(1/1222),0,0⟩,⟨(49/109),(-1/109),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1111 : CertBound := ⟨false,true,⟨⟨(210400854500/1526263336169),(-10382610500/1526263336169),0,0⟩,⟨(12542/28787),(1/86361),0,0⟩,⟨(984/2257),(-1/2257),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1126 : CertBound := ⟨false,true,⟨⟨(359490461150/1636553162387),(1650599750/1636553162387),0,0⟩,⟨(6265/14278),(-1/14278),0,0⟩,⟨(16112/36661),(1/36661),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private abbrev sourceBound1142 : CertBound := ⟨false,true,⟨⟨(228931/687489),(44448/229163),0,0⟩,⟨(109/251),(1/753),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private abbrev sourceBound1143 : CertBound := ⟨false,true,⟨⟨(263287960500/786278842063),(-21629154500/786278842063),0,0⟩,⟨(16112/36661),(1/36661),0,0⟩,⟨(402/913),(-1/913),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

open Freiman
open Freiman
namespace SourceMemo20_1
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,1,[1],([2],[3]),false,[(([3],[1]),true)],([1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound276,sourceBound804,sourceBound862,sourceBound1142]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : ([sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound276,sourceBound804,sourceBound862,sourceBound1142] ++ [sourceBound276]).eraseDups = expected[0] := by
  have hdup : sourceBound276 ∈ expected[0] := by simp [expected]
  change (expected[0] ++ [sourceBound276]).eraseDups = expected[0]
  rw [List.eraseDups_append, erase0,
    BindingSourceSupport20.singleton_removeAll_of_mem hdup,
    List.eraseDups_nil, List.append_nil]
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_1.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b21 := sourceBound21) (b260 := sourceBound260) (b275 := sourceBound275) (b276 := sourceBound276) (b371 := sourceBound371) (b440 := sourceBound440) (b442 := sourceBound442) (b804 := sourceBound804) (b843 := sourceBound843) (b856 := sourceBound856) (b862 := sourceBound862) (b1142 := sourceBound1142)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG0.2.1) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm1 BindingNumeric20.pullKey2 BindingNumeric20.pullKey3 BindingNumeric20.pullKey4 eraseActual0)
end SourceMemo20_1

open Freiman
open Freiman
namespace SourceMemo20_2
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,2,[1],([2],[3]),false,[(([3],[1]),false),(([3],[]),true),(([],[1]),false)],([1,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound1107,sourceBound399,sourceBound650,sourceBound1067,sourceBound392,sourceBound627,sourceBound718,sourceBound984,sourceBound177]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound1107,sourceBound399,sourceBound650,sourceBound1067,sourceBound392,sourceBound627,sourceBound718,sourceBound984,sourceBound177].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_2.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b7 := sourceBound7) (b21 := sourceBound21) (b177 := sourceBound177) (b260 := sourceBound260) (b275 := sourceBound275) (b371 := sourceBound371) (b392 := sourceBound392) (b399 := sourceBound399) (b440 := sourceBound440) (b442 := sourceBound442) (b627 := sourceBound627) (b650 := sourceBound650) (b718 := sourceBound718) (b814 := sourceBound814) (b843 := sourceBound843) (b856 := sourceBound856) (b984 := sourceBound984) (b1067 := sourceBound1067) (b1107 := sourceBound1107)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG0.2.2.1) (BindingSourceBranches20.branchesG0.2.2.2.1) (BindingSourceBranches20.branchesG0.2.2.2.2.1) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm2 BindingNumeric20.pull5 BindingNumeric20.norm3 BindingNumeric20.pullKey6 BindingNumeric20.norm4 BindingNumeric20.pullKey7 BindingNumeric20.pullKey8 BindingNumeric20.pullKey9 eraseActual0)
end SourceMemo20_2

open Freiman
open Freiman
namespace SourceMemo20_3
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,3,[1],([2],[3]),false,[(([3],[1]),false),(([2],[]),true),(([],[1]),false)],([1,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound1107,sourceBound406,sourceBound697,sourceBound1094,sourceBound391,sourceBound646,sourceBound754,sourceBound1016,sourceBound176],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound1107,sourceBound406,sourceBound697,sourceBound230,sourceBound740,sourceBound658,sourceBound1111,sourceBound391,sourceBound646,sourceBound754,sourceBound1016,sourceBound176],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound239,sourceBound850,sourceBound406,sourceBound697,sourceBound1094,sourceBound391,sourceBound646,sourceBound754,sourceBound1016,sourceBound176],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound239,sourceBound850,sourceBound406,sourceBound697,sourceBound230,sourceBound740,sourceBound658,sourceBound1111,sourceBound391,sourceBound646,sourceBound754,sourceBound1016,sourceBound176]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound1107,sourceBound406,sourceBound697,sourceBound1094,sourceBound391,sourceBound646,sourceBound754,sourceBound1016,sourceBound176].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound1107,sourceBound406,sourceBound697,sourceBound230,sourceBound740,sourceBound658,sourceBound1111,sourceBound391,sourceBound646,sourceBound754,sourceBound1016,sourceBound176].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem erase2 : expected[2].eraseDups = expected[2] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[2] (by simp [expected])))
private theorem eraseActual2 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound239,sourceBound850,sourceBound406,sourceBound697,sourceBound1094,sourceBound391,sourceBound646,sourceBound754,sourceBound1016,sourceBound176].eraseDups = expected[2] := by
  simpa [expected] using erase2
private theorem erase3 : expected[3].eraseDups = expected[3] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[3] (by simp [expected])))
private theorem eraseActual3 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound239,sourceBound850,sourceBound406,sourceBound697,sourceBound230,sourceBound740,sourceBound658,sourceBound1111,sourceBound391,sourceBound646,sourceBound754,sourceBound1016,sourceBound176].eraseDups = expected[3] := by
  simpa [expected] using erase3
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_3.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b7 := sourceBound7) (b21 := sourceBound21) (b176 := sourceBound176) (b230 := sourceBound230) (b239 := sourceBound239) (b260 := sourceBound260) (b275 := sourceBound275) (b371 := sourceBound371) (b391 := sourceBound391) (b406 := sourceBound406) (b440 := sourceBound440) (b442 := sourceBound442) (b646 := sourceBound646) (b658 := sourceBound658) (b697 := sourceBound697) (b740 := sourceBound740) (b754 := sourceBound754) (b814 := sourceBound814) (b843 := sourceBound843) (b850 := sourceBound850) (b856 := sourceBound856) (b1016 := sourceBound1016) (b1094 := sourceBound1094) (b1107 := sourceBound1107) (b1111 := sourceBound1111)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG0.2.2.1) (BindingSourceBranches20.branchesG0.2.2.2.2.2.1) (BindingSourceBranches20.branchesG0.2.2.2.2.2.2.1) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm2 BindingNumeric20.pull5 BindingNumeric20.pullKey5 BindingNumeric20.pullKey10 BindingNumeric20.norm5 BindingNumeric20.pullKey11 BindingNumeric20.pull13 BindingNumeric20.pullKey12 BindingNumeric20.pullKey13 BindingNumeric20.pullKey14 BindingNumeric20.norm6 BindingNumeric20.pullKey15 BindingNumeric20.pullKey16 BindingNumeric20.pullKey17 eraseActual0 eraseActual1 eraseActual2 eraseActual3)
end SourceMemo20_3

open Freiman
open Freiman
namespace SourceMemo20_4
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,4,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),true),(([],[1]),false)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound264,sourceBound788,sourceBound1126,sourceBound404,sourceBound699,sourceBound803,sourceBound1065,sourceBound207],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound264,sourceBound788,sourceBound251,sourceBound793,sourceBound729,sourceBound1143,sourceBound404,sourceBound699,sourceBound803,sourceBound1065,sourceBound207]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound264,sourceBound788,sourceBound1126,sourceBound404,sourceBound699,sourceBound803,sourceBound1065,sourceBound207].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound264,sourceBound788,sourceBound251,sourceBound793,sourceBound729,sourceBound1143,sourceBound404,sourceBound699,sourceBound803,sourceBound1065,sourceBound207].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_4.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b7 := sourceBound7) (b21 := sourceBound21) (b207 := sourceBound207) (b251 := sourceBound251) (b260 := sourceBound260) (b264 := sourceBound264) (b275 := sourceBound275) (b371 := sourceBound371) (b404 := sourceBound404) (b440 := sourceBound440) (b442 := sourceBound442) (b699 := sourceBound699) (b729 := sourceBound729) (b788 := sourceBound788) (b793 := sourceBound793) (b803 := sourceBound803) (b814 := sourceBound814) (b843 := sourceBound843) (b856 := sourceBound856) (b1065 := sourceBound1065) (b1126 := sourceBound1126) (b1143 := sourceBound1143)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG0.2.2.1) (BindingSourceBranches20.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches20.branchesG1.1) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm2 BindingNumeric20.norm7 BindingNumeric20.pullKey18 BindingNumeric20.pull21 BindingNumeric20.pullKey19 BindingNumeric20.pullKey20 BindingNumeric20.pullKey21 BindingNumeric20.norm8 BindingNumeric20.pullKey22 BindingNumeric20.pullKey23 BindingNumeric20.pullKey24 eraseActual0 eraseActual1)
end SourceMemo20_4

open Freiman
open Freiman
namespace SourceMemo20_5
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,5,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound807,sourceBound19,sourceBound766,sourceBound1106,sourceBound393,sourceBound621,sourceBound767,sourceBound1022,sourceBound178]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport20.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport20.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport20.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound275,sourceBound442,sourceBound814,sourceBound7,sourceBound807,sourceBound19,sourceBound766,sourceBound1106,sourceBound393,sourceBound621,sourceBound767,sourceBound1022,sourceBound178].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps20_5.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b7 := sourceBound7) (b19 := sourceBound19) (b21 := sourceBound21) (b178 := sourceBound178) (b260 := sourceBound260) (b275 := sourceBound275) (b371 := sourceBound371) (b393 := sourceBound393) (b440 := sourceBound440) (b442 := sourceBound442) (b621 := sourceBound621) (b766 := sourceBound766) (b767 := sourceBound767) (b807 := sourceBound807) (b814 := sourceBound814) (b843 := sourceBound843) (b856 := sourceBound856) (b1022 := sourceBound1022) (b1106 := sourceBound1106)
      BindingSourceSupport20.relaxed1 BindingNumeric20.initial_base (BindingSourceBranches20.branchesG0.1) (BindingSourceBranches20.branchesG0.2.2.1) (BindingSourceBranches20.branchesG1.2.1) (BindingSourceBranches20.branchesG1.2.2.1) BindingNumeric20.norm0 BindingNumeric20.pullKey0 BindingNumeric20.pull1 BindingNumeric20.norm2 BindingNumeric20.norm9 BindingNumeric20.pullKey25 BindingNumeric20.pullKey26 BindingNumeric20.norm10 BindingNumeric20.pullKey27 BindingNumeric20.pullKey28 BindingNumeric20.pullKey29 eraseActual0)
end SourceMemo20_5

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
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
private def path1 : LowerHistoryPath := ⟨.left,1,[1],([2],[3]),false,[(([3],[1]),true)],([1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem records1 : lowerHistoryRecordsFor path1 = [⟨.left,1,0,(-1),false,494,1186⟩] := by
  change lowerHistoryRecordsFor (⟨.left,1,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 1, lowerHistoryRecordsL_list] <;> rfl
private def path2 : LowerHistoryPath := ⟨.left,2,[1],([2],[3]),false,[(([3],[1]),false),(([3],[]),true),(([],[1]),false)],([1,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem records2 : lowerHistoryRecordsFor path2 = [⟨.left,2,0,(-1),false,221,1132⟩] := by
  change lowerHistoryRecordsFor (⟨.left,2,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 2, lowerHistoryRecordsL_list] <;> rfl
private def path3 : LowerHistoryPath := ⟨.left,3,[1],([2],[3]),false,[(([3],[1]),false),(([2],[]),true),(([],[1]),false)],([1,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private theorem records3 : lowerHistoryRecordsFor path3 = [⟨.left,3,0,(-1),false,219,1138⟩,⟨.left,3,1,(-1),false,215,1138⟩,⟨.left,3,2,(-1),false,217,1138⟩,⟨.left,3,3,(-1),false,213,1138⟩] := by
  change lowerHistoryRecordsFor (⟨.left,3,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 3, lowerHistoryRecordsL_list] <;> rfl
private def path4 : LowerHistoryPath := ⟨.left,4,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),true),(([],[1]),false)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private theorem records4 : lowerHistoryRecordsFor path4 = [⟨.left,4,0,(-1),false,227,1174⟩,⟨.left,4,1,(-1),false,225,1174⟩] := by
  change lowerHistoryRecordsFor (⟨.left,4,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 4, lowerHistoryRecordsL_list] <;> rfl
private def path5 : LowerHistoryPath := ⟨.left,5,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem records5 : lowerHistoryRecordsFor path5 = [⟨.left,5,0,(-1),false,207,1156⟩] := by
  change lowerHistoryRecordsFor (⟨.left,5,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 5, lowerHistoryRecordsL_list] <;> rfl
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
private theorem bound176 : lowerHistoryBound 176 = sourceBound176 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[175]? = some sourceBound176 := Eq.refl (some sourceBound176)
  exact (BoundCompact16.global_to_chunk1 175 (by decide)).trans hlocal
private theorem bound177 : lowerHistoryBound 177 = sourceBound177 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[176]? = some sourceBound177 := Eq.refl (some sourceBound177)
  exact (BoundCompact16.global_to_chunk1 176 (by decide)).trans hlocal
private theorem bound178 : lowerHistoryBound 178 = sourceBound178 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[177]? = some sourceBound178 := Eq.refl (some sourceBound178)
  exact (BoundCompact16.global_to_chunk1 177 (by decide)).trans hlocal
private theorem bound207 : lowerHistoryBound 207 = sourceBound207 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[6]? = some sourceBound207 := Eq.refl (some sourceBound207)
  exact (BoundCompact16.global_to_chunk2 6 (by decide)).trans hlocal
private theorem bound230 : lowerHistoryBound 230 = sourceBound230 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[29]? = some sourceBound230 := Eq.refl (some sourceBound230)
  exact (BoundCompact16.global_to_chunk2 29 (by decide)).trans hlocal
private theorem bound239 : lowerHistoryBound 239 = sourceBound239 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[38]? = some sourceBound239 := Eq.refl (some sourceBound239)
  exact (BoundCompact16.global_to_chunk2 38 (by decide)).trans hlocal
private theorem bound251 : lowerHistoryBound 251 = sourceBound251 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[50]? = some sourceBound251 := Eq.refl (some sourceBound251)
  exact (BoundCompact16.global_to_chunk2 50 (by decide)).trans hlocal
private theorem bound260 : lowerHistoryBound 260 = sourceBound260 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[59]? = some sourceBound260 := Eq.refl (some sourceBound260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hlocal
private theorem bound264 : lowerHistoryBound 264 = sourceBound264 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[63]? = some sourceBound264 := Eq.refl (some sourceBound264)
  exact (BoundCompact16.global_to_chunk2 63 (by decide)).trans hlocal
private theorem bound275 : lowerHistoryBound 275 = sourceBound275 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[74]? = some sourceBound275 := Eq.refl (some sourceBound275)
  exact (BoundCompact16.global_to_chunk2 74 (by decide)).trans hlocal
private theorem bound276 : lowerHistoryBound 276 = sourceBound276 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[75]? = some sourceBound276 := Eq.refl (some sourceBound276)
  exact (BoundCompact16.global_to_chunk2 75 (by decide)).trans hlocal
private theorem bound371 : lowerHistoryBound 371 = sourceBound371 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[170]? = some sourceBound371 := Eq.refl (some sourceBound371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hlocal
private theorem bound391 : lowerHistoryBound 391 = sourceBound391 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[190]? = some sourceBound391 := Eq.refl (some sourceBound391)
  exact (BoundCompact16.global_to_chunk2 190 (by decide)).trans hlocal
private theorem bound392 : lowerHistoryBound 392 = sourceBound392 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[191]? = some sourceBound392 := Eq.refl (some sourceBound392)
  exact (BoundCompact16.global_to_chunk2 191 (by decide)).trans hlocal
private theorem bound393 : lowerHistoryBound 393 = sourceBound393 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[192]? = some sourceBound393 := Eq.refl (some sourceBound393)
  exact (BoundCompact16.global_to_chunk2 192 (by decide)).trans hlocal
private theorem bound399 : lowerHistoryBound 399 = sourceBound399 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[198]? = some sourceBound399 := Eq.refl (some sourceBound399)
  exact (BoundCompact16.global_to_chunk2 198 (by decide)).trans hlocal
private theorem bound404 : lowerHistoryBound 404 = sourceBound404 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[3]? = some sourceBound404 := Eq.refl (some sourceBound404)
  exact (BoundCompact16.global_to_chunk3 3 (by decide)).trans hlocal
private theorem bound406 : lowerHistoryBound 406 = sourceBound406 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[5]? = some sourceBound406 := Eq.refl (some sourceBound406)
  exact (BoundCompact16.global_to_chunk3 5 (by decide)).trans hlocal
private theorem bound440 : lowerHistoryBound 440 = sourceBound440 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[39]? = some sourceBound440 := Eq.refl (some sourceBound440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hlocal
private theorem bound442 : lowerHistoryBound 442 = sourceBound442 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[41]? = some sourceBound442 := Eq.refl (some sourceBound442)
  exact (BoundCompact16.global_to_chunk3 41 (by decide)).trans hlocal
private theorem bound621 : lowerHistoryBound 621 = sourceBound621 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[20]? = some sourceBound621 := Eq.refl (some sourceBound621)
  exact (BoundCompact16.global_to_chunk4 20 (by decide)).trans hlocal
private theorem bound627 : lowerHistoryBound 627 = sourceBound627 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[26]? = some sourceBound627 := Eq.refl (some sourceBound627)
  exact (BoundCompact16.global_to_chunk4 26 (by decide)).trans hlocal
private theorem bound646 : lowerHistoryBound 646 = sourceBound646 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[45]? = some sourceBound646 := Eq.refl (some sourceBound646)
  exact (BoundCompact16.global_to_chunk4 45 (by decide)).trans hlocal
private theorem bound650 : lowerHistoryBound 650 = sourceBound650 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[49]? = some sourceBound650 := Eq.refl (some sourceBound650)
  exact (BoundCompact16.global_to_chunk4 49 (by decide)).trans hlocal
private theorem bound658 : lowerHistoryBound 658 = sourceBound658 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[57]? = some sourceBound658 := Eq.refl (some sourceBound658)
  exact (BoundCompact16.global_to_chunk4 57 (by decide)).trans hlocal
private theorem bound697 : lowerHistoryBound 697 = sourceBound697 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[96]? = some sourceBound697 := Eq.refl (some sourceBound697)
  exact (BoundCompact16.global_to_chunk4 96 (by decide)).trans hlocal
private theorem bound699 : lowerHistoryBound 699 = sourceBound699 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[98]? = some sourceBound699 := Eq.refl (some sourceBound699)
  exact (BoundCompact16.global_to_chunk4 98 (by decide)).trans hlocal
private theorem bound718 : lowerHistoryBound 718 = sourceBound718 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[117]? = some sourceBound718 := Eq.refl (some sourceBound718)
  exact (BoundCompact16.global_to_chunk4 117 (by decide)).trans hlocal
private theorem bound729 : lowerHistoryBound 729 = sourceBound729 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[128]? = some sourceBound729 := Eq.refl (some sourceBound729)
  exact (BoundCompact16.global_to_chunk4 128 (by decide)).trans hlocal
private theorem bound740 : lowerHistoryBound 740 = sourceBound740 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[139]? = some sourceBound740 := Eq.refl (some sourceBound740)
  exact (BoundCompact16.global_to_chunk4 139 (by decide)).trans hlocal
private theorem bound754 : lowerHistoryBound 754 = sourceBound754 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[153]? = some sourceBound754 := Eq.refl (some sourceBound754)
  exact (BoundCompact16.global_to_chunk4 153 (by decide)).trans hlocal
private theorem bound766 : lowerHistoryBound 766 = sourceBound766 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[165]? = some sourceBound766 := Eq.refl (some sourceBound766)
  exact (BoundCompact16.global_to_chunk4 165 (by decide)).trans hlocal
private theorem bound767 : lowerHistoryBound 767 = sourceBound767 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[166]? = some sourceBound767 := Eq.refl (some sourceBound767)
  exact (BoundCompact16.global_to_chunk4 166 (by decide)).trans hlocal
private theorem bound788 : lowerHistoryBound 788 = sourceBound788 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[187]? = some sourceBound788 := Eq.refl (some sourceBound788)
  exact (BoundCompact16.global_to_chunk4 187 (by decide)).trans hlocal
private theorem bound793 : lowerHistoryBound 793 = sourceBound793 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[192]? = some sourceBound793 := Eq.refl (some sourceBound793)
  exact (BoundCompact16.global_to_chunk4 192 (by decide)).trans hlocal
private theorem bound803 : lowerHistoryBound 803 = sourceBound803 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[2]? = some sourceBound803 := Eq.refl (some sourceBound803)
  exact (BoundCompact16.global_to_chunk5 2 (by decide)).trans hlocal
private theorem bound804 : lowerHistoryBound 804 = sourceBound804 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[3]? = some sourceBound804 := Eq.refl (some sourceBound804)
  exact (BoundCompact16.global_to_chunk5 3 (by decide)).trans hlocal
private theorem bound807 : lowerHistoryBound 807 = sourceBound807 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[6]? = some sourceBound807 := Eq.refl (some sourceBound807)
  exact (BoundCompact16.global_to_chunk5 6 (by decide)).trans hlocal
private theorem bound814 : lowerHistoryBound 814 = sourceBound814 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[13]? = some sourceBound814 := Eq.refl (some sourceBound814)
  exact (BoundCompact16.global_to_chunk5 13 (by decide)).trans hlocal
private theorem bound843 : lowerHistoryBound 843 = sourceBound843 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[42]? = some sourceBound843 := Eq.refl (some sourceBound843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hlocal
private theorem bound850 : lowerHistoryBound 850 = sourceBound850 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[49]? = some sourceBound850 := Eq.refl (some sourceBound850)
  exact (BoundCompact16.global_to_chunk5 49 (by decide)).trans hlocal
private theorem bound856 : lowerHistoryBound 856 = sourceBound856 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[55]? = some sourceBound856 := Eq.refl (some sourceBound856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hlocal
private theorem bound862 : lowerHistoryBound 862 = sourceBound862 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[61]? = some sourceBound862 := Eq.refl (some sourceBound862)
  exact (BoundCompact16.global_to_chunk5 61 (by decide)).trans hlocal
private theorem bound984 : lowerHistoryBound 984 = sourceBound984 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[183]? = some sourceBound984 := Eq.refl (some sourceBound984)
  exact (BoundCompact16.global_to_chunk5 183 (by decide)).trans hlocal
private theorem bound1016 : lowerHistoryBound 1016 = sourceBound1016 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[15]? = some sourceBound1016 := Eq.refl (some sourceBound1016)
  exact (BoundCompact16.global_to_chunk6 15).trans hlocal
private theorem bound1022 : lowerHistoryBound 1022 = sourceBound1022 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[21]? = some sourceBound1022 := Eq.refl (some sourceBound1022)
  exact (BoundCompact16.global_to_chunk6 21).trans hlocal
private theorem bound1065 : lowerHistoryBound 1065 = sourceBound1065 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[64]? = some sourceBound1065 := Eq.refl (some sourceBound1065)
  exact (BoundCompact16.global_to_chunk6 64).trans hlocal
private theorem bound1067 : lowerHistoryBound 1067 = sourceBound1067 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[66]? = some sourceBound1067 := Eq.refl (some sourceBound1067)
  exact (BoundCompact16.global_to_chunk6 66).trans hlocal
private theorem bound1094 : lowerHistoryBound 1094 = sourceBound1094 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[93]? = some sourceBound1094 := Eq.refl (some sourceBound1094)
  exact (BoundCompact16.global_to_chunk6 93).trans hlocal
private theorem bound1106 : lowerHistoryBound 1106 = sourceBound1106 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[105]? = some sourceBound1106 := Eq.refl (some sourceBound1106)
  exact (BoundCompact16.global_to_chunk6 105).trans hlocal
private theorem bound1107 : lowerHistoryBound 1107 = sourceBound1107 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[106]? = some sourceBound1107 := Eq.refl (some sourceBound1107)
  exact (BoundCompact16.global_to_chunk6 106).trans hlocal
private theorem bound1111 : lowerHistoryBound 1111 = sourceBound1111 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[110]? = some sourceBound1111 := Eq.refl (some sourceBound1111)
  exact (BoundCompact16.global_to_chunk6 110).trans hlocal
private theorem bound1126 : lowerHistoryBound 1126 = sourceBound1126 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[125]? = some sourceBound1126 := Eq.refl (some sourceBound1126)
  exact (BoundCompact16.global_to_chunk6 125).trans hlocal
private theorem bound1142 : lowerHistoryBound 1142 = sourceBound1142 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[141]? = some sourceBound1142 := Eq.refl (some sourceBound1142)
  exact (BoundCompact16.global_to_chunk6 141).trans hlocal
private theorem bound1143 : lowerHistoryBound 1143 = sourceBound1143 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[142]? = some sourceBound1143 := Eq.refl (some sourceBound1143)
  exact (BoundCompact16.global_to_chunk6 142).trans hlocal
end BatchLookup20

open Freiman
namespace SourceValues20
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem source1 : lowerHistorySourcePremises BatchLookup20.path1 =
    ([[371,843,260,440,3,856,21,275,442,276,804,862,1142]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound276 (congrArg₂ List.cons BatchLookup20.bound804 (congrArg₂ List.cons BatchLookup20.bound862 (congrArg₂ List.cons BatchLookup20.bound1142 (rfl : ([] : List CertBound) = [])))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo20_1.source.trans hb.symm
private theorem length1 : BatchLookup20.path1.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path1).length := by
  exact (congrArg List.length source1).symm
private theorem source2 : lowerHistorySourcePremises BatchLookup20.path2 =
    ([[371,843,260,440,3,856,21,275,442,814,7,1107,399,650,1067,392,627,718,984,177]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound814 (congrArg₂ List.cons BatchLookup20.bound7 (congrArg₂ List.cons BatchLookup20.bound1107 (congrArg₂ List.cons BatchLookup20.bound399 (congrArg₂ List.cons BatchLookup20.bound650 (congrArg₂ List.cons BatchLookup20.bound1067 (congrArg₂ List.cons BatchLookup20.bound392 (congrArg₂ List.cons BatchLookup20.bound627 (congrArg₂ List.cons BatchLookup20.bound718 (congrArg₂ List.cons BatchLookup20.bound984 (congrArg₂ List.cons BatchLookup20.bound177 (rfl : ([] : List CertBound) = []))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo20_2.source.trans hb.symm
private theorem length2 : BatchLookup20.path2.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path2).length := by
  exact (congrArg List.length source2).symm
private theorem source3 : lowerHistorySourcePremises BatchLookup20.path3 =
    ([[371,843,260,440,3,856,21,275,442,814,7,1107,406,697,1094,391,646,754,1016,176],[371,843,260,440,3,856,21,275,442,814,7,1107,406,697,230,740,658,1111,391,646,754,1016,176],[371,843,260,440,3,856,21,275,442,814,7,239,850,406,697,1094,391,646,754,1016,176],[371,843,260,440,3,856,21,275,442,814,7,239,850,406,697,230,740,658,1111,391,646,754,1016,176]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound814 (congrArg₂ List.cons BatchLookup20.bound7 (congrArg₂ List.cons BatchLookup20.bound1107 (congrArg₂ List.cons BatchLookup20.bound406 (congrArg₂ List.cons BatchLookup20.bound697 (congrArg₂ List.cons BatchLookup20.bound1094 (congrArg₂ List.cons BatchLookup20.bound391 (congrArg₂ List.cons BatchLookup20.bound646 (congrArg₂ List.cons BatchLookup20.bound754 (congrArg₂ List.cons BatchLookup20.bound1016 (congrArg₂ List.cons BatchLookup20.bound176 (rfl : ([] : List CertBound) = []))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound814 (congrArg₂ List.cons BatchLookup20.bound7 (congrArg₂ List.cons BatchLookup20.bound1107 (congrArg₂ List.cons BatchLookup20.bound406 (congrArg₂ List.cons BatchLookup20.bound697 (congrArg₂ List.cons BatchLookup20.bound230 (congrArg₂ List.cons BatchLookup20.bound740 (congrArg₂ List.cons BatchLookup20.bound658 (congrArg₂ List.cons BatchLookup20.bound1111 (congrArg₂ List.cons BatchLookup20.bound391 (congrArg₂ List.cons BatchLookup20.bound646 (congrArg₂ List.cons BatchLookup20.bound754 (congrArg₂ List.cons BatchLookup20.bound1016 (congrArg₂ List.cons BatchLookup20.bound176 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound814 (congrArg₂ List.cons BatchLookup20.bound7 (congrArg₂ List.cons BatchLookup20.bound239 (congrArg₂ List.cons BatchLookup20.bound850 (congrArg₂ List.cons BatchLookup20.bound406 (congrArg₂ List.cons BatchLookup20.bound697 (congrArg₂ List.cons BatchLookup20.bound1094 (congrArg₂ List.cons BatchLookup20.bound391 (congrArg₂ List.cons BatchLookup20.bound646 (congrArg₂ List.cons BatchLookup20.bound754 (congrArg₂ List.cons BatchLookup20.bound1016 (congrArg₂ List.cons BatchLookup20.bound176 (rfl : ([] : List CertBound) = [])))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound814 (congrArg₂ List.cons BatchLookup20.bound7 (congrArg₂ List.cons BatchLookup20.bound239 (congrArg₂ List.cons BatchLookup20.bound850 (congrArg₂ List.cons BatchLookup20.bound406 (congrArg₂ List.cons BatchLookup20.bound697 (congrArg₂ List.cons BatchLookup20.bound230 (congrArg₂ List.cons BatchLookup20.bound740 (congrArg₂ List.cons BatchLookup20.bound658 (congrArg₂ List.cons BatchLookup20.bound1111 (congrArg₂ List.cons BatchLookup20.bound391 (congrArg₂ List.cons BatchLookup20.bound646 (congrArg₂ List.cons BatchLookup20.bound754 (congrArg₂ List.cons BatchLookup20.bound1016 (congrArg₂ List.cons BatchLookup20.bound176 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))))
  exact SourceMemo20_3.source.trans hb.symm
private theorem length3 : BatchLookup20.path3.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path3).length := by
  exact (congrArg List.length source3).symm
private theorem source4 : lowerHistorySourcePremises BatchLookup20.path4 =
    ([[371,843,260,440,3,856,21,275,442,814,7,264,788,1126,404,699,803,1065,207],[371,843,260,440,3,856,21,275,442,814,7,264,788,251,793,729,1143,404,699,803,1065,207]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound814 (congrArg₂ List.cons BatchLookup20.bound7 (congrArg₂ List.cons BatchLookup20.bound264 (congrArg₂ List.cons BatchLookup20.bound788 (congrArg₂ List.cons BatchLookup20.bound1126 (congrArg₂ List.cons BatchLookup20.bound404 (congrArg₂ List.cons BatchLookup20.bound699 (congrArg₂ List.cons BatchLookup20.bound803 (congrArg₂ List.cons BatchLookup20.bound1065 (congrArg₂ List.cons BatchLookup20.bound207 (rfl : ([] : List CertBound) = [])))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound814 (congrArg₂ List.cons BatchLookup20.bound7 (congrArg₂ List.cons BatchLookup20.bound264 (congrArg₂ List.cons BatchLookup20.bound788 (congrArg₂ List.cons BatchLookup20.bound251 (congrArg₂ List.cons BatchLookup20.bound793 (congrArg₂ List.cons BatchLookup20.bound729 (congrArg₂ List.cons BatchLookup20.bound1143 (congrArg₂ List.cons BatchLookup20.bound404 (congrArg₂ List.cons BatchLookup20.bound699 (congrArg₂ List.cons BatchLookup20.bound803 (congrArg₂ List.cons BatchLookup20.bound1065 (congrArg₂ List.cons BatchLookup20.bound207 (rfl : ([] : List CertBound) = []))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))
  exact SourceMemo20_4.source.trans hb.symm
private theorem length4 : BatchLookup20.path4.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path4).length := by
  exact (congrArg List.length source4).symm
private theorem source5 : lowerHistorySourcePremises BatchLookup20.path5 =
    ([[371,843,260,440,3,856,21,275,442,814,7,807,19,766,1106,393,621,767,1022,178]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup20.bound371 (congrArg₂ List.cons BatchLookup20.bound843 (congrArg₂ List.cons BatchLookup20.bound260 (congrArg₂ List.cons BatchLookup20.bound440 (congrArg₂ List.cons BatchLookup20.bound3 (congrArg₂ List.cons BatchLookup20.bound856 (congrArg₂ List.cons BatchLookup20.bound21 (congrArg₂ List.cons BatchLookup20.bound275 (congrArg₂ List.cons BatchLookup20.bound442 (congrArg₂ List.cons BatchLookup20.bound814 (congrArg₂ List.cons BatchLookup20.bound7 (congrArg₂ List.cons BatchLookup20.bound807 (congrArg₂ List.cons BatchLookup20.bound19 (congrArg₂ List.cons BatchLookup20.bound766 (congrArg₂ List.cons BatchLookup20.bound1106 (congrArg₂ List.cons BatchLookup20.bound393 (congrArg₂ List.cons BatchLookup20.bound621 (congrArg₂ List.cons BatchLookup20.bound767 (congrArg₂ List.cons BatchLookup20.bound1022 (congrArg₂ List.cons BatchLookup20.bound178 (rfl : ([] : List CertBound) = []))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo20_5.source.trans hb.symm
private theorem length5 : BatchLookup20.path5.alternatives =
    (lowerHistorySourcePremises BatchLookup20.path5).length := by
  exact (congrArg List.length source5).symm
end SourceValues20


namespace PremiseCompact50

variable {α : Type} (a b c d e f : Array α)
  (ha : a.size = 200) (hb : b.size = 200) (hc : c.size = 200)
  (hd : d.size = 200) (he : e.size = 200)
include ha hb hc hd he

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
private theorem premise207 : lowerHistoryPremises[206]? = some ([3,7,19,21,178,260,275,371,393,440,442,621,766,767,807,814,843,856,1022,1106] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 206 = 200+6 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 6 (by decide)]
  rfl
private theorem premise213 : lowerHistoryPremises[212]? = some ([3,7,21,176,230,239,260,275,371,391,406,440,442,646,658,697,740,754,814,843,850,856,1016,1111] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 212 = 200+12 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 12 (by decide)]
  rfl
private theorem premise215 : lowerHistoryPremises[214]? = some ([3,7,21,176,230,260,275,371,391,406,440,442,646,658,697,740,754,814,843,856,1016,1107,1111] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 214 = 200+14 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 14 (by decide)]
  rfl
private theorem premise217 : lowerHistoryPremises[216]? = some ([3,7,21,176,239,260,275,371,391,406,440,442,646,697,754,814,843,850,856,1016,1094] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 216 = 200+16 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 16 (by decide)]
  rfl
private theorem premise219 : lowerHistoryPremises[218]? = some ([3,7,21,176,260,275,371,391,406,440,442,646,697,754,814,843,856,1016,1094,1107] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 218 = 200+18 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 18 (by decide)]
  rfl
private theorem premise221 : lowerHistoryPremises[220]? = some ([3,7,21,177,260,275,371,392,399,440,442,627,650,718,814,843,856,984,1067,1107] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 220 = 200+20 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 20 (by decide)]
  rfl
private theorem premise225 : lowerHistoryPremises[224]? = some ([3,7,21,207,251,260,264,275,371,404,440,442,699,729,788,793,803,814,843,856,1065,1143] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 224 = 200+24 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 24 (by decide)]
  rfl
private theorem premise227 : lowerHistoryPremises[226]? = some ([3,7,21,207,260,264,275,371,404,440,442,699,788,803,814,843,856,1065,1126] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 226 = 200+26 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 26 (by decide)]
  rfl
private theorem premise494 : lowerHistoryPremises[493]? = some ([3,21,260,275,276,371,440,442,804,843,856,862,1142] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 493 = 400+93 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 93 (by decide)]
  rfl
end BatchLookup20

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
namespace ExtrasMemo15
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,39,[1],([2],[3]),false,[(([2],[]),true),(([1],[]),false)],([1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
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

private theorem coverage1 : (List.range path1.alternatives).all (coverageCheck path1 ([⟨.left,1,0,(-1),false,494,1186⟩] : List LowerHistoryRecord)) = true := by decide +kernel


private theorem coverage2 : (List.range path2.alternatives).all (coverageCheck path2 ([⟨.left,2,0,(-1),false,221,1132⟩] : List LowerHistoryRecord)) = true := by decide +kernel


private theorem coverage3 : (List.range path3.alternatives).all (coverageCheck path3 ([⟨.left,3,0,(-1),false,219,1138⟩,⟨.left,3,1,(-1),false,215,1138⟩,⟨.left,3,2,(-1),false,217,1138⟩,⟨.left,3,3,(-1),false,213,1138⟩] : List LowerHistoryRecord)) = true := by decide +kernel


private theorem coverage4 : (List.range path4.alternatives).all (coverageCheck path4 ([⟨.left,4,0,(-1),false,227,1174⟩,⟨.left,4,1,(-1),false,225,1174⟩] : List LowerHistoryRecord)) = true := by decide +kernel


private theorem coverage5 : (List.range path5.alternatives).all (coverageCheck path5 ([⟨.left,5,0,(-1),false,207,1156⟩] : List LowerHistoryRecord)) = true := by decide +kernel


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
private theorem pathsL_list : lowerHistoryPathsL.toList = [
⟨.left,1,[1],([2],[3]),false,[(([3],[1]),true)],([1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,2,[1],([2],[3]),false,[(([3],[1]),false),(([3],[]),true),(([],[1]),false)],([1,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,3,[1],([2],[3]),false,[(([3],[1]),false),(([2],[]),true),(([],[1]),false)],([1,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,4,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),true),(([],[1]),false)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,5,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,6,[1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([1],[]),true)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,7,[1],([2],[3]),false,[(([2],[1]),true)],([1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,8,[1],([2],[3]),false,[(([2],[1]),false),(([3],[]),true),(([],[1]),false)],([1,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,9,[1],([2],[3]),false,[(([2],[1]),false),(([2],[]),true),(([],[1]),false)],([1,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,10,[1],([2],[3]),false,[(([2],[1]),false),(([1],[]),true),(([],[1]),false)],([1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,11,[1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([3],[]),true)],([1,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,12,[1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true)],([1,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,13,[1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true)],([1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,14,[1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,15,[1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,16,[1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,3,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,17,[1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,3,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,18,[1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,3,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,19,[1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,20,[1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([1,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,21,[1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([1,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,22,[1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,23,[1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,24,[1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,25,[1],([2],[3]),false,[(([3],[]),true),(([1],[]),false)],([1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,26,[1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([1,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,27,[1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([1,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,28,[1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,29,[1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,2,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,30,[1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,16⟩,
⟨.left,31,[1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,2,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,8⟩,
⟨.left,32,[1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,8⟩,
⟨.left,33,[1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([1,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,34,[1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([1,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,8⟩,
⟨.left,35,[1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,36,[1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([1,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,37,[1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([1,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,38,[1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,39,[1],([2],[3]),false,[(([2],[]),true),(([1],[]),false)],([1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,40,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,41,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,42,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,43,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,44,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,8⟩,
⟨.left,45,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,46,[1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,47,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,48,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,49,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,50,[1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩,
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
⟨.left,100,[2],([2],[3]),false,[(([3],[1]),true)],([2,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
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
⟨.left,150,[2],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([2,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,151,[2],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,152,[2],([2],[3]),false,[(([1],[]),true),(([1],[]),false)],([2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,153,[2],([2],[3]),false,[(([1],[]),false),(([3],[1]),true),(([],[1]),false)],([2,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,3⟩,
⟨.left,154,[2],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([3],[]),true)],([2,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,3⟩,
⟨.left,155,[2],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([2],[]),true)],([2,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,3⟩,
⟨.left,156,[2],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),true)],([2,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,3⟩,
⟨.left,157,[2],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,12⟩,
⟨.left,158,[2],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,6⟩,
⟨.left,159,[2],([2],[3]),false,[(([1],[]),false),(([2],[1]),true),(([],[1]),false)],([2,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,160,[2],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([3],[]),true)],([2,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,161,[2],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([2],[]),true)],([2,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,162,[2],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),true)],([2,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,163,[2],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,164,[2],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,165,[2],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,166,[2],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([3],[]),true),(([],[1]),false)],([2,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,167,[2],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,168,[2],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,169,[2],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([3],[]),true)],([2,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,170,[2],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([2],[]),true)],([2,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,171,[2],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([1],[]),true)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,172,[2],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([3],[]),true)],([2,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,173,[2],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([2],[]),true)],([2,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,174,[2],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true)],([2,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,175,[2],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,176,[2],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,177,[2],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),false),(([],[1]),false)],([2,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,178,[2],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([3],[]),true)],([2,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,179,[2],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([2],[]),true)],([2,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,180,[2],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),true)],([2,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,181,[2],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,182,[2],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,183,[2],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,184,[2],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),false),(([],[1]),false)],([2,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,185,[2],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([3],[]),true)],([2,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,186,[2],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([2],[]),true)],([2,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,187,[2],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),true)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,188,[2],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,189,[2],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,190,[2],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,191,[2],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),false),(([],[1]),false)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,192,[2],([2],[3]),true,[(([1],[]),true),(([3],[]),true)],([2,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,193,[2],([2],[3]),true,[(([1],[]),true),(([2],[]),true)],([2,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,194,[2],([2],[3]),true,[(([1],[]),true),(([1],[]),true)],([2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,195,[2],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([2,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,1⟩,
⟨.left,196,[2],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([2,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,4⟩,
⟨.left,197,[2],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([2,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,198,[2],([2],[3]),true,[(([1],[]),false),(([],[1]),false)],([2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/3),(1/2),(3/4),(4/5)⟩,2⟩,
⟨.left,199,[3],([2],[3]),false,[(([3],[1]),true)],([3,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,200,[3],([2],[3]),false,[(([3],[1]),false),(([3],[]),true),(([],[1]),false)],([3,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,201,[3],([2],[3]),false,[(([3],[1]),false),(([2],[]),true),(([],[1]),false)],([3,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,202,[3],([2],[3]),false,[(([3],[1]),false),(([1],[]),true),(([],[1]),false)],([3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,203,[3],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([3,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,204,[3],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([1],[]),true)],([3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,205,[3],([2],[3]),false,[(([2],[1]),true)],([3,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,206,[3],([2],[3]),false,[(([2],[1]),false),(([3],[]),true),(([],[1]),false)],([3,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,207,[3],([2],[3]),false,[(([2],[1]),false),(([2],[]),true),(([],[1]),false)],([3,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,208,[3],([2],[3]),false,[(([2],[1]),false),(([1],[]),true),(([],[1]),false)],([3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,209,[3],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([3],[]),true)],([3,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,210,[3],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true)],([3,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,211,[3],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true)],([3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,212,[3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,213,[3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,214,[3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,2,3,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,215,[3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,2,3,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,216,[3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,2,3,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,217,[3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,218,[3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,219,[3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,220,[3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,221,[3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,222,[3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,223,[3],([2],[3]),false,[(([3],[]),true),(([1],[]),false)],([3,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,224,[3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([3,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,225,[3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,226,[3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,227,[3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,2,2,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,228,[3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,16⟩,
⟨.left,229,[3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,2,2,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,8⟩,
⟨.left,230,[3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,8⟩,
⟨.left,231,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,232,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,8⟩,
⟨.left,233,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,234,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,235,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,236,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,237,[3],([2],[3]),false,[(([2],[]),true),(([1],[]),false)],([3,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,238,[3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([3,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,239,[3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,240,[3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,241,[3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,242,[3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,8⟩,
⟨.left,243,[3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,244,[3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,245,[3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,246,[3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,247,[3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,248,[3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,249,[3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,250,[3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,251,[3],([2],[3]),false,[(([1],[]),true),(([1],[]),false)],([3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,252,[3],([2],[3]),false,[(([1],[]),false),(([3],[1]),true),(([],[1]),false)],([3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,3⟩,
⟨.left,253,[3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([3],[]),true)],([3,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,3⟩,
⟨.left,254,[3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([2],[]),true)],([3,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,3⟩,
⟨.left,255,[3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),true)],([3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,3⟩,
⟨.left,256,[3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,12⟩,
⟨.left,257,[3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,6⟩,
⟨.left,258,[3],([2],[3]),false,[(([1],[]),false),(([2],[1]),true),(([],[1]),false)],([3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,259,[3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([3],[]),true)],([3,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,260,[3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([2],[]),true)],([3,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,261,[3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),true)],([3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,262,[3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,263,[3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,264,[3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,265,[3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([3],[]),true),(([],[1]),false)],([3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,266,[3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([2],[]),true),(([],[1]),false)],([3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,267,[3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),true),(([],[1]),false)],([3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,268,[3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([3],[]),true)],([3,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,269,[3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([2],[]),true)],([3,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,270,[3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([1],[]),true)],([3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,271,[3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([3],[]),true)],([3,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,272,[3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([2],[]),true)],([3,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,273,[3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true)],([3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,274,[3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,275,[3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,276,[3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),false),(([],[1]),false)],([3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,277,[3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([3],[]),true)],([3,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,278,[3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([2],[]),true)],([3,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,279,[3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),true)],([3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,280,[3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,281,[3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,282,[3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,283,[3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),false),(([],[1]),false)],([3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,284,[3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([3],[]),true)],([3,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,285,[3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([2],[]),true)],([3,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,286,[3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),true)],([3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,287,[3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,288,[3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,289,[3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,290,[3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),false),(([],[1]),false)],([3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,291,[3],([2],[3]),true,[(([1],[]),true),(([3],[]),true)],([3,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,292,[3],([2],[3]),true,[(([1],[]),true),(([2],[]),true)],([3,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,293,[3],([2],[3]),true,[(([1],[]),true),(([1],[]),true)],([3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,294,[3],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,1⟩,
⟨.left,295,[3],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,4⟩,
⟨.left,296,[3],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,297,[3],([2],[3]),true,[(([1],[]),false),(([],[1]),false)],([3,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/4),(1/3),(3/4),(4/5)⟩,2⟩,
⟨.left,298,[3,1],([2],[3]),false,[(([3],[1]),true)],([3,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,299,[3,1],([2],[3]),false,[(([3],[1]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,300,[3,1],([2],[3]),false,[(([3],[1]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,301,[3,1],([2],[3]),false,[(([3],[1]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,302,[3,1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,303,[3,1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,304,[3,1],([2],[3]),false,[(([2],[1]),true)],([3,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,305,[3,1],([2],[3]),false,[(([2],[1]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,306,[3,1],([2],[3]),false,[(([2],[1]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,307,[3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,308,[3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([3],[]),true)],([3,1,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,309,[3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,310,[3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,311,[3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,312,[3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,313,[3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,3,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,314,[3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,3,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,315,[3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,3,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,316,[3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,317,[3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,1,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,318,[3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,1,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,319,[3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,320,[3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,321,[3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,322,[3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),false)],([3,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,323,[3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([3,1,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,324,[3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,1,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,325,[3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,326,[3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,2,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,327,[3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,16⟩,
⟨.left,328,[3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,2,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,8⟩,
⟨.left,329,[3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,8⟩,
⟨.left,330,[3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,1,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,331,[3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,1,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,8⟩,
⟨.left,332,[3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,333,[3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,334,[3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,335,[3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,336,[3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),false)],([3,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,337,[3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([3,1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,338,[3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,339,[3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,340,[3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,341,[3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,8⟩,
⟨.left,342,[3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,343,[3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,344,[3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,345,[3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,346,[3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,347,[3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,348,[3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,349,[3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,350,[3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),false)],([3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,351,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),true),(([],[1]),false)],([3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,3⟩,
⟨.left,352,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([3],[]),true)],([3,1,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,3⟩,
⟨.left,353,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([2],[]),true)],([3,1,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,3⟩,
⟨.left,354,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),true)],([3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,3⟩,
⟨.left,355,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,12⟩,
⟨.left,356,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,6⟩,
⟨.left,357,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),true),(([],[1]),false)],([3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,358,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([3],[]),true)],([3,1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,359,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([2],[]),true)],([3,1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,360,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),true)],([3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,361,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,362,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,363,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,364,[3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,365,[3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,366,[3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,367,[3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([3],[]),true)],([3,1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,368,[3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,369,[3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,370,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([3],[]),true)],([3,1,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,371,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([2],[]),true)],([3,1,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,372,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,373,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,374,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,375,[3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),false),(([],[1]),false)],([3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,376,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([3],[]),true)],([3,1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,377,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([2],[]),true)],([3,1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,378,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,379,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,380,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,381,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,382,[3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),false),(([],[1]),false)],([3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,383,[3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([3],[]),true)],([3,1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,384,[3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([2],[]),true)],([3,1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,385,[3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,386,[3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,387,[3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,388,[3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,389,[3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),false),(([],[1]),false)],([3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,390,[3,1],([2],[3]),true,[(([1],[]),true),(([3],[]),true)],([3,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,391,[3,1],([2],[3]),true,[(([1],[]),true),(([2],[]),true)],([3,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,392,[3,1],([2],[3]),true,[(([1],[]),true),(([1],[]),true)],([3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,393,[3,1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,1⟩,
⟨.left,394,[3,1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,4⟩,
⟨.left,395,[3,1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,396,[3,1],([2],[3]),true,[(([1],[]),false),(([],[1]),false)],([3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(3/4),(4/5),(3/4),(4/5)⟩,2⟩,
⟨.left,397,[3,1,3],([2],[3]),false,[(([3],[1]),true)],([3,1,3,2,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,398,[3,1,3],([2],[3]),false,[(([3],[1]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,399,[3,1,3],([2],[3]),false,[(([3],[1]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,400,[3,1,3],([2],[3]),false,[(([3],[1]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,401,[3,1,3],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,3,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,402,[3,1,3],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,403,[3,1,3],([2],[3]),false,[(([2],[1]),true)],([3,1,3,2,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,404,[3,1,3],([2],[3]),false,[(([2],[1]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,405,[3,1,3],([2],[3]),false,[(([2],[1]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,406,[3,1,3],([2],[3]),false,[(([2],[1]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,407,[3,1,3],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([3],[]),true)],([3,1,3,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,408,[3,1,3],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,3,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,409,[3,1,3],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,410,[3,1,3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,1,3,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,411,[3,1,3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,412,[3,1,3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,3,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,413,[3,1,3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,3,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,414,[3,1,3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,3,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,415,[3,1,3],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,416,[3,1,3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,1,3,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,417,[3,1,3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,1,3,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,418,[3,1,3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,419,[3,1,3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,3,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,420,[3,1,3],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,3,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,421,[3,1,3],([2],[3]),false,[(([3],[]),true),(([1],[]),false)],([3,1,3,2,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,422,[3,1,3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([3,1,3,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,423,[3,1,3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,1,3,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,424,[3,1,3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,425,[3,1,3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,2,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,426,[3,1,3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,16⟩,
⟨.left,427,[3,1,3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,2,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,8⟩,
⟨.left,428,[3,1,3],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,8⟩,
⟨.left,429,[3,1,3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,1,3,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,430,[3,1,3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,1,3,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,8⟩,
⟨.left,431,[3,1,3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,432,[3,1,3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,3,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,433,[3,1,3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,3,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,434,[3,1,3],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,3,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,435,[3,1,3],([2],[3]),false,[(([2],[]),true),(([1],[]),false)],([3,1,3,2,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,436,[3,1,3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([3,1,3,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,437,[3,1,3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,1,3,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,438,[3,1,3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,439,[3,1,3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,440,[3,1,3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,8⟩,
⟨.left,441,[3,1,3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,442,[3,1,3],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,443,[3,1,3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,1,3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,444,[3,1,3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,1,3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,445,[3,1,3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,446,[3,1,3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,3,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,447,[3,1,3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,3,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,448,[3,1,3],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,449,[3,1,3],([2],[3]),false,[(([1],[]),true),(([1],[]),false)],([3,1,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,450,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[1]),true),(([],[1]),false)],([3,1,3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,3⟩,
⟨.left,451,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([3],[]),true)],([3,1,3,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,3⟩,
⟨.left,452,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([2],[]),true)],([3,1,3,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,3⟩,
⟨.left,453,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),true)],([3,1,3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,3⟩,
⟨.left,454,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,12⟩,
⟨.left,455,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,6⟩,
⟨.left,456,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[1]),true),(([],[1]),false)],([3,1,3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,457,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([3],[]),true)],([3,1,3,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,458,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([2],[]),true)],([3,1,3,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,459,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),true)],([3,1,3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,460,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,461,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,462,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,463,[3,1,3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,464,[3,1,3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,465,[3,1,3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,466,[3,1,3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([3],[]),true)],([3,1,3,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,467,[3,1,3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,3,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,468,[3,1,3],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,469,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([3],[]),true)],([3,1,3,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,470,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([2],[]),true)],([3,1,3,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,471,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,472,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,473,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,474,[3,1,3],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),false),(([],[1]),false)],([3,1,3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,475,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([3],[]),true)],([3,1,3,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,476,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([2],[]),true)],([3,1,3,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,477,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,478,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,479,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,480,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,481,[3,1,3],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),false),(([],[1]),false)],([3,1,3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,482,[3,1,3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([3],[]),true)],([3,1,3,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,483,[3,1,3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([2],[]),true)],([3,1,3,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,484,[3,1,3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,485,[3,1,3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,486,[3,1,3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,487,[3,1,3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,488,[3,1,3],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),false),(([],[1]),false)],([3,1,3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,489,[3,1,3],([2],[3]),true,[(([1],[]),true),(([3],[]),true)],([3,1,3,2,3],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,490,[3,1,3],([2],[3]),true,[(([1],[]),true),(([2],[]),true)],([3,1,3,2,2],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,491,[3,1,3],([2],[3]),true,[(([1],[]),true),(([1],[]),true)],([3,1,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,492,[3,1,3],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,1⟩,
⟨.left,493,[3,1,3],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,4⟩,
⟨.left,494,[3,1,3],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,495,[3,1,3],([2],[3]),true,[(([1],[]),false),(([],[1]),false)],([3,1,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(5/19),(4/15),(3/4),(4/5)⟩,2⟩,
⟨.left,496,[3,1,3,1],([2],[3]),false,[(([3],[1]),true)],([3,1,3,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,497,[3,1,3,1],([2],[3]),false,[(([3],[1]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,498,[3,1,3,1],([2],[3]),false,[(([3],[1]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,499,[3,1,3,1],([2],[3]),false,[(([3],[1]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,500,[3,1,3,1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,3,1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,501,[3,1,3,1],([2],[3]),false,[(([3],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,502,[3,1,3,1],([2],[3]),false,[(([2],[1]),true)],([3,1,3,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,503,[3,1,3,1],([2],[3]),false,[(([2],[1]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,504,[3,1,3,1],([2],[3]),false,[(([2],[1]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,505,[3,1,3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,506,[3,1,3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([3],[]),true)],([3,1,3,1,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,507,[3,1,3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,3,1,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,508,[3,1,3,1],([2],[3]),false,[(([2],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,509,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,1,3,1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,510,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,511,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,3,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,512,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,3,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,513,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,3,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,514,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,515,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,3,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,516,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,3,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,517,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,518,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,3,1,2,3,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,519,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,3,1,2,3,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,520,[3,1,3,1],([2],[3]),false,[(([3],[]),true),(([1],[]),false)],([3,1,3,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,521,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([3,1,3,1,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,522,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,1,3,1,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,523,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,524,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,2,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,525,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,2,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,16⟩,
⟨.left,526,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,2,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,8⟩,
⟨.left,527,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,8⟩,
⟨.left,528,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,2,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,529,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,2,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,8⟩,
⟨.left,530,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,531,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,3,1,2,2,1,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,532,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,3,1,2,2,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,533,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,3,1,2,2,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,534,[3,1,3,1],([2],[3]),false,[(([2],[]),true),(([1],[]),false)],([3,1,3,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,535,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([3],[]),true)],([3,1,3,1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,536,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([2],[]),true)],([3,1,3,1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,537,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),true)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,538,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,539,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,8⟩,
⟨.left,540,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,541,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([],[1]),false),(([1],[]),false),(([],[1]),false)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,542,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,543,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,544,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,545,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true)],([3,1,3,1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,546,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true)],([3,1,3,1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,547,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,548,[3,1,3,1],([2],[3]),false,[(([1],[]),true),(([1],[]),false)],([3,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,549,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),true),(([],[1]),false)],([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,3⟩,
⟨.left,550,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([3],[]),true)],([3,1,3,1,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,3⟩,
⟨.left,551,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([2],[]),true)],([3,1,3,1,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,3⟩,
⟨.left,552,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),true)],([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,3⟩,
⟨.left,553,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,12⟩,
⟨.left,554,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,6⟩,
⟨.left,555,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,556,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([3],[]),true)],([3,1,3,1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,557,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([2],[]),true)],([3,1,3,1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,558,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),true)],([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,559,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,560,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,561,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,562,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,563,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,564,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,565,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([3],[]),true)],([3,1,3,1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,566,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([2],[]),true)],([3,1,3,1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,567,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([],[1]),false),(([1],[]),false),(([1],[]),true)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,568,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([3],[]),true)],([3,1,3,1,2,1,3,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,569,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([2],[]),true)],([3,1,3,1,2,1,3,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,570,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,571,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,572,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,573,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),false),(([],[1]),false)],([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,574,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([3],[]),true)],([3,1,3,1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,575,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([2],[]),true)],([3,1,3,1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,576,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,577,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,578,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,579,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,580,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),false),(([],[1]),false)],([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,581,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([3],[]),true)],([3,1,3,1,2,1,1,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,582,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([2],[]),true)],([3,1,3,1,2,1,1,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,583,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),true)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,584,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,1,1,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,585,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,1,1,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,586,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,1,1,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,587,[3,1,3,1],([2],[3]),false,[(([1],[]),false),(([1],[]),true),(([1],[]),false),(([],[1]),false)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,588,[3,1,3,1],([2],[3]),true,[(([1],[]),true),(([3],[]),true)],([3,1,3,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,589,[3,1,3,1],([2],[3]),true,[(([1],[]),true),(([2],[]),true)],([3,1,3,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,590,[3,1,3,1],([2],[3]),true,[(([1],[]),true),(([1],[]),true)],([3,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,591,[3,1,3,1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([3,1,3,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,1⟩,
⟨.left,592,[3,1,3,1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([3,1,3,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,4⟩,
⟨.left,593,[3,1,3,1],([2],[3]),true,[(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([3,1,3,1,2,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩,
⟨.left,594,[3,1,3,1],([2],[3]),true,[(([1],[]),false),(([],[1]),false)],([3,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(15/19),(19/24),(3/4),(4/5)⟩,2⟩
] := by rfl
private theorem first_lookup (i : Nat) (h : i < 50) :
    lowerHistoryPaths[i]? = lowerHistoryPathsL[i]? := by
  apply append5_get
  rw [sizeL]
  omega
private theorem path1_lookup : lowerHistoryPaths[0]? = some path1 := by
  rw [first_lookup 0 (by decide), ← Array.getElem?_toList, pathsL_list]
  rfl
private theorem path2_lookup : lowerHistoryPaths[1]? = some path2 := by
  rw [first_lookup 1 (by decide), ← Array.getElem?_toList, pathsL_list]
  rfl
private theorem path3_lookup : lowerHistoryPaths[2]? = some path3 := by
  rw [first_lookup 2 (by decide), ← Array.getElem?_toList, pathsL_list]
  rfl
private theorem path4_lookup : lowerHistoryPaths[3]? = some path4 := by
  rw [first_lookup 3 (by decide), ← Array.getElem?_toList, pathsL_list]
  rfl
private theorem path5_lookup : lowerHistoryPaths[4]? = some path5 := by
  rw [first_lookup 4 (by decide), ← Array.getElem?_toList, pathsL_list]
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

namespace WitnessLookup20
private theorem witness1132_projection :
    (lowerHistoryWitness 1132).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1132).upperBound = lowerHistoryBound 984 ∧
    (lowerHistoryWitness 1132).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[131]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 984, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 984, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 131)).trans hl
private theorem witness1138_projection :
    (lowerHistoryWitness 1138).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1138).upperBound = lowerHistoryBound 1016 ∧
    (lowerHistoryWitness 1138).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[137]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1016, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1016, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 137)).trans hl
private theorem witness1156_projection :
    (lowerHistoryWitness 1156).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1156).upperBound = lowerHistoryBound 1022 ∧
    (lowerHistoryWitness 1156).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[155]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1022, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1022, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 155)).trans hl
private theorem witness1174_projection :
    (lowerHistoryWitness 1174).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1174).upperBound = lowerHistoryBound 1065 ∧
    (lowerHistoryWitness 1174).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[173]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1065, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1065, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 173)).trans hl
private theorem witness1186_projection :
    (lowerHistoryWitness 1186).lowerBound = lowerHistoryBound 442 ∧
    (lowerHistoryWitness 1186).upperBound = lowerHistoryBound 1142 ∧
    (lowerHistoryWitness 1186).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses06[185]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 442, lowerHistoryBound 1142, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) := Eq.refl (some (lowerHistoryBound 442, lowerHistoryBound 1142, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape) (WitnessCompact16.global_to_chunk6 185)).trans hl
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
private def src1 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,276,804,862,1142]]
private def recs1 : List LowerHistoryRecord := [⟨.left,1,0,(-1),false,494,1186⟩]
private theorem check1 : recs1.all (recordCheck path1 src1 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path1_binding : lowerHistoryPathBinding path1 := by
  apply pathBinding_from_ids path1 src1 [] recs1 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source1 rfl records1 rfl
  · intro r hr _
    simp only [recs1, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise494)
  · intro r hr _
    simp only [recs1, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path1] using WitnessLookup20.witness1186_projection
  · exact check1
  · exact BatchCoverage15.coverage_sound path1 recs1
      records1 SourceValues20.length1 BatchCoverageAll20.coverage1
private def src2 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,814,7,1107,399,650,1067,392,627,718,984,177]]
private def recs2 : List LowerHistoryRecord := [⟨.left,2,0,(-1),false,221,1132⟩]
private theorem check2 : recs2.all (recordCheck path2 src2 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path2_binding : lowerHistoryPathBinding path2 := by
  apply pathBinding_from_ids path2 src2 [] recs2 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source2 rfl records2 rfl
  · intro r hr _
    simp only [recs2, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise221)
  · intro r hr _
    simp only [recs2, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path2] using WitnessLookup20.witness1132_projection
  · exact check2
  · exact BatchCoverage15.coverage_sound path2 recs2
      records2 SourceValues20.length2 BatchCoverageAll20.coverage2
private def src3 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,814,7,1107,406,697,1094,391,646,754,1016,176],[371,843,260,440,3,856,21,275,442,814,7,1107,406,697,230,740,658,1111,391,646,754,1016,176],[371,843,260,440,3,856,21,275,442,814,7,239,850,406,697,1094,391,646,754,1016,176],[371,843,260,440,3,856,21,275,442,814,7,239,850,406,697,230,740,658,1111,391,646,754,1016,176]]
private def recs3 : List LowerHistoryRecord := [⟨.left,3,0,(-1),false,219,1138⟩,⟨.left,3,1,(-1),false,215,1138⟩,⟨.left,3,2,(-1),false,217,1138⟩,⟨.left,3,3,(-1),false,213,1138⟩]
private theorem check3 : recs3.all (recordCheck path3 src3 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path3_binding : lowerHistoryPathBinding path3 := by
  apply pathBinding_from_ids path3 src3 [] recs3 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source3 rfl records3 rfl
  · intro r hr _
    simp only [recs3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise219)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise215)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise217)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise213)
  · intro r hr _
    simp only [recs3, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [wids, path3] using WitnessLookup20.witness1138_projection
    · simpa only [wids, path3] using WitnessLookup20.witness1138_projection
    · simpa only [wids, path3] using WitnessLookup20.witness1138_projection
    · simpa only [wids, path3] using WitnessLookup20.witness1138_projection
  · exact check3
  · exact BatchCoverage15.coverage_sound path3 recs3
      records3 SourceValues20.length3 BatchCoverageAll20.coverage3
private def src4 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,814,7,264,788,1126,404,699,803,1065,207],[371,843,260,440,3,856,21,275,442,814,7,264,788,251,793,729,1143,404,699,803,1065,207]]
private def recs4 : List LowerHistoryRecord := [⟨.left,4,0,(-1),false,227,1174⟩,⟨.left,4,1,(-1),false,225,1174⟩]
private theorem check4 : recs4.all (recordCheck path4 src4 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path4_binding : lowerHistoryPathBinding path4 := by
  apply pathBinding_from_ids path4 src4 [] recs4 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source4 rfl records4 rfl
  · intro r hr _
    simp only [recs4, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise227)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise225)
  · intro r hr _
    simp only [recs4, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [wids, path4] using WitnessLookup20.witness1174_projection
    · simpa only [wids, path4] using WitnessLookup20.witness1174_projection
  · exact check4
  · exact BatchCoverage15.coverage_sound path4 recs4
      records4 SourceValues20.length4 BatchCoverageAll20.coverage4
private def src5 : List (List Nat) := [[371,843,260,440,3,856,21,275,442,814,7,807,19,766,1106,393,621,767,1022,178]]
private def recs5 : List LowerHistoryRecord := [⟨.left,5,0,(-1),false,207,1156⟩]
private theorem check5 : recs5.all (recordCheck path5 src5 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path5_binding : lowerHistoryPathBinding path5 := by
  apply pathBinding_from_ids path5 src5 [] recs5 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues20.source5 rfl records5 rfl
  · intro r hr _
    simp only [recs5, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise207)
  · intro r hr _
    simp only [recs5, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path5] using WitnessLookup20.witness1156_projection
  · exact check5
  · exact BatchCoverage15.coverage_sound path5 recs5
      records5 SourceValues20.length5 BatchCoverageAll20.coverage5
end BatchIdSolution0
theorem _root_.solution : lowerHistoryBindingBatch 0 5 := by
  intro i hlo hhi p hp
  interval_cases i
  · have he := Option.some.inj (PathLookup20.path1_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path1_binding
  · have he := Option.some.inj (PathLookup20.path2_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path2_binding
  · have he := Option.some.inj (PathLookup20.path3_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path3_binding
  · have he := Option.some.inj (PathLookup20.path4_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path4_binding
  · have he := Option.some.inj (PathLookup20.path5_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution0.path5_binding
end M7Binding0Sep15
#print axioms solution
