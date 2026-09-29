-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0060_0065
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T09:51:47.279666+00:00
-- url     : https://prove2.me/submissions/814fd1d9-bf16-4986-8ce2-7fbcbb2de9c5

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
private theorem norm7 : lowerHistoryNormalization ([2,1],[3]) false false = ⟨false,false,⟨⟨(7/10),0,0,(1/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm21 : lowerHistoryNormalization ([2,1,2],[3,1]) false false = ⟨false,false,⟨⟨(41/185),0,0,(32/1295)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm22 : lowerHistoryNormalization ([2,1,2,3],[3,1]) true true = ⟨true,true,⟨⟨(3211/109150),0,0,(49/109150)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm23 : lowerHistoryNormalization ([2,1,2,2],[3,1]) true true = ⟨true,true,⟨⟨(1671/46166),0,0,(1475/323162)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm24 : lowerHistoryNormalization ([2,1,2,1],[3,1]) true false = ⟨true,false,⟨⟨(15/134),0,0,(23/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm25 : lowerHistoryNormalization ([2,1,2,1],[3,1]) false false = ⟨false,false,⟨⟨(15/134),0,0,(23/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm26 : lowerHistoryNormalization ([2,1,2,1,3],[3,1]) true true = ⟨true,true,⟨⟨(1689/35690),0,0,(-1817/249830)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm27 : lowerHistoryNormalization ([2,1,2,1,3,1],[3,1]) true true = ⟨true,true,⟨⟨(75/1747),0,0,(-496/61145)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(6391/17470),0,0,(-1/17470)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm28 : lowerHistoryNormalization ([2,1,2,1,2],[3,1]) true true = ⟨true,true,⟨⟨(551/34277),0,0,(414/239939)⟩,⟨(109/302),0,0,(1/906)⟩,⟨(167/454),0,0,(-1/3178)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm29 : lowerHistoryNormalization ([2,1,2,1,2,1],[3,1]) true true = ⟨true,true,⟨⟨(11731/1422118),0,0,(433/1422118)⟩,⟨(109/302),0,0,(1/906)⟩,⟨(3453/9418),0,0,(-1/9418)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey11 : lowerHistoryPull (lowerHistoryH2) ([2,1],[3]) false = ⟨true,true,⟨⟨(3418287291/5478244850),(-26216794/8217367275),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey12 : lowerHistoryPull (lowerHistoryH5) ([2,1],[3]) false = ⟨false,true,⟨⟨(33285470319/67820291500),(-327225429/33910145750),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey49 : lowerHistoryPull (lowerHistoryH7) ([2,1,2,1],[3,1]) true = ⟨false,false,⟨⟨(1890656950/2826713021),(-538238350/2826713021),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey50 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,1],[3,1]) true = ⟨false,true,⟨⟨(785697/8289481),(1373204/24868443),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey51 : lowerHistoryPull (lowerHistoryHN) ([2,1,2,1],[3,1]) true = ⟨true,false,⟨⟨(15/134),0,0,(23/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey52 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) false = ⟨false,false,⟨⟨(154748703689/531731481700),(100050183/265865740850),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey53 : lowerHistoryPull (lowerHistoryH5) ([2,1,2],[3,1]) false = ⟨false,true,⟨⟨(12740018571/65624465320),(6136962399/1640611633000),0,0⟩,⟨(5491/14843),(1/44529),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey54 : lowerHistoryPull (lowerHistoryH6) ([2,1,2],[3,1]) false = ⟨false,true,⟨⟨(1641924483/15716862500),0,0,(246790851/31433725000)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(3913/10550),0,0,(-1/31650)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey55 : lowerHistoryPull (lowerHistoryH7Mixed) ([2,1,2],[3,1]) false = ⟨false,true,⟨⟨(3187478/35004125),(1328733/70008250),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(616/1657),(-1/1657),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey56 : lowerHistoryPull (lowerHistoryH7) ([2,1,2,3],[3,1]) true = ⟨false,false,⟨⟨(2709504850/17611227007),(-2273395150/52833681021),0,0⟩,⟨(4178/11269),(1/11269),0,0⟩,⟨(1701/4583),(-1/13749),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey57 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,3],[3,1]) true = ⟨false,true,⟨⟨(3436033/154937481),(667124/51645827),0,0⟩,⟨(4178/11269),(1/11269),0,0⟩,⟨(1701/4583),(-1/13749),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey58 : lowerHistoryPull (lowerHistoryHN) ([2,1,2,3],[3,1]) true = ⟨true,false,⟨⟨(3211/109150),0,0,(49/109150)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey59 : lowerHistoryPull (lowerHistoryH7) ([2,1,2,2],[3,1]) true = ⟨false,false,⟨⟨(114542650/408037531),(-96533350/1224112593),0,0⟩,⟨(735/1991),(1/5973),0,0⟩,⟨(2890/7813),(-1/7813),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey60 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,2],[3,1]) true = ⟨false,true,⟨⟨(1880401/46667049),(365108/15555683),0,0⟩,⟨(735/1991),(1/5973),0,0⟩,⟨(2890/7813),(-1/7813),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey61 : lowerHistoryPull (lowerHistoryHN) ([2,1,2,2],[3,1]) true = ⟨true,false,⟨⟨(1671/46166),0,0,(1475/323162)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey62 : lowerHistoryPull (lowerHistoryH7) ([2,1,2,1],[3,1]) false = ⟨true,false,⟨⟨(194269963/5454255300),(2189251/218170212),0,0⟩,⟨(439/1202),(1/3606),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey63 : lowerHistoryPull (lowerHistoryH2) ([2,1,2,1,3],[3,1]) true = ⟨false,true,⟨⟨(1516196471650/87327732407149),(31597917350/261983197221447),0,0⟩,⟨(63631/174094),(-1/174094),0,0⟩,⟨(58649/160439),(1/481317),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey64 : lowerHistoryPull (lowerHistoryH7) ([2,1,2,1,3,1],[3,1]) true = ⟨false,false,⟨⟨(7353418800/256083887081),(-6298235450/768251661243),0,0⟩,⟨(6565/17963),(1/53889),0,0⟩,⟨(30565/83614),(-1/83614),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey65 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,1,3,1],[3,1]) true = ⟨false,true,⟨⟨(18283513/4505874846),(10652047/4505874846),0,0⟩,⟨(6565/17963),(1/53889),0,0⟩,⟨(30565/83614),(-1/83614),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey66 : lowerHistoryPull (lowerHistoryHN) ([2,1,2,1,3,1],[3,1]) true = ⟨true,false,⟨⟨(75/1747),0,0,(-496/61145)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(6391/17470),0,0,(-1/17470)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey67 : lowerHistoryPull (lowerHistoryH9) ([2,1,2,1],[3,1]) false = ⟨false,false,⟨⟨(1186584/30433),(-683411/30433),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey68 : lowerHistoryPull (lowerHistoryH2) ([2,1,2,1,2],[3,1]) true = ⟨false,true,⟨⟨(416400055300/14271340563181),(2655398800/14271340563181),0,0⟩,⟨(38250/104497),(-1/104497),0,0⟩,⟨(103957/283933),(1/283933),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey69 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,2,1,2],[3,1]) true = ⟨false,false,⟨⟨(7584289377500/205055504298333),(166270436500/205055504298333),0,0⟩,⟨(103957/283933),(1/283933),0,0⟩,⟨(5298/14461),(-1/14461),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey70 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,1,2,1,2],[3,1]) true = ⟨false,false,⟨⟨(17496401/1450108957),(201423059/17401307484),0,0⟩,⟨(2241/6122),(1/18366),0,0⟩,⟨(173564/473737),(-1/473737),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey71 : lowerHistoryPull (lowerHistoryH23) ([2,1,2,1,2],[3,1]) true = ⟨false,true,⟨⟨(12332455500/296039619187),(-509955500/296039619187),0,0⟩,⟨(103957/283933),(1/283933),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey72 : lowerHistoryPull (lowerHistoryH7) ([2,1,2,1,2,1],[3,1]) true = ⟨false,false,⟨⟨(26349523850/548964322709),(-7502818050/548964322709),0,0⟩,⟨(11929/32593),(1/32593),0,0⟩,⟨(18084/49393),(-1/49393),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey73 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,1,2,1],[3,1]) true = ⟨false,true,⟨⟨(10947811/1609866049),(19134112/4829598147),0,0⟩,⟨(11929/32593),(1/32593),0,0⟩,⟨(18084/49393),(-1/49393),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey74 : lowerHistoryPull (lowerHistoryHN) ([2,1,2,1,2,1],[3,1]) true = ⟨true,false,⟨⟨(11731/1422118),0,0,(433/1422118)⟩,⟨(109/302),0,0,(1/906)⟩,⟨(3453/9418),0,0,(-1/9418)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pull11 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = ⟨false,false,⟨⟨(3418287291/5478244850),(-26216794/8217367275),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey11]
  rfl
private theorem pull16 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) false = ⟨true,false,⟨⟨(33285470319/67820291500),(-327225429/33910145750),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey12]
  rfl
private theorem pull68 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH7) ([2,1,2,1],[3,1]) false = ⟨false,true,⟨⟨(194269963/5454255300),(2189251/218170212),0,0⟩,⟨(439/1202),(1/3606),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey62]
  rfl
private theorem pull76 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,2,1,2],[3,1]) true = ⟨true,false,⟨⟨(416400055300/14271340563181),(2655398800/14271340563181),0,0⟩,⟨(38250/104497),(-1/104497),0,0⟩,⟨(103957/283933),(1/283933),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey68]
  rfl
end BindingNumeric16
set_option Elab.async false

open Freiman
namespace BindingSourceBranches16
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem branchesG0 :
    (lowerHistoryNecessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1],[3]) = some [⟨false,false,⟨⟨(16971/22607),(33730/22607),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1],[3,1]) = some [⟨true,false,⟨⟨(-605239/322621),(452861/322621),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1],[3,1]) = some [⟨true,false,⟨⟨(-2396241/3388429),(1794784/3388429),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,1,2],[3,1]) = some [⟨false,false,⟨⟨(405277/4216979),(1100652/4216979),0,0⟩,⟨(553/1429),(1/1429),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(188333/700271),(1121999/2100813),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1],[3,1]) = some [⟨false,false,⟨⟨(43019/22607),(82570/22607),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [⟨true,false,⟨⟨(-27041/364702),(168601/1094106),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩]) := by
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
private theorem branchesG3 :
    (lowerHistoryNecessary ⟨⟨([1,2,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,2,1],[3,1]) = some [⟨false,false,⟨⟨(214600/1533493),(1183231/4600479),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,2,1],[3,1]) = some [⟨true,false,⟨⟨(-25544163/190658063),(19094857/190658063),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,2,1,3],[3,1]) = some [⟨false,false,⟨⟨(7185630/680098211),(52919348/2040294633),0,0⟩,⟨(439/1202),(1/3606),0,0⟩,⟨(63631/174094),(-1/174094),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,2,1,3,1],[3,1]) = some [⟨false,false,⟨⟨(295645379/34737062867),(221489974/34737062867),0,0⟩,⟨(63631/174094),(-1/174094),0,0⟩,⟨(11220/30697),(1/30697),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,2,1,2],[3,1]) = some [⟨false,false,⟨⟨(312097/17559841),(879473/17559841),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,2,1,2,1],[3,1]) = some [⟨false,false,⟨⟨(231057/22960561),(1270246/68881683),0,0⟩,⟨(2241/6122),(1/18366),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,2,1,1],[3,1]) = some [⟨false,false,⟨⟨(1449541/30335747),(3003540/30335747),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,2,1,1,1],[3,1]) = some [⟨false,false,⟨⟨(8076301/422628973),(15924509/422628973),0,0⟩,⟨(3370/9181),(1/9181),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
  decide +kernel
end BindingSourceBranches16

open Freiman
namespace BindingSourceSupport16
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem relaxed1 : lowerHistoryRelaxedGoodness ⟨([1],[3,1]),(false,false)⟩ = some [⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩] := by
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
namespace BindingOps16_61
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b11 : CertBound) (b21 : CertBound) (b43 : CertBound) (b183 : CertBound) (b260 : CertBound) (b272 : CertBound) (b371 : CertBound) (b395 : CertBound) (b440 : CertBound) (b620 : CertBound) (b753 : CertBound) (b774 : CertBound) (b789 : CertBound) (b824 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1015 : CertBound) (b1088 : CertBound) (b1098 : CertBound) (b1118 : CertBound)
private def path : LowerHistoryPath := ⟨.left,61,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([3],[]),true)],([1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [b11])
    (hb3 : ops.necessary ⟨⟨([1,2,1,2,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,2,3],[3,1]) = some [b620])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) false = b272)
    (hn4 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) false = b789)
    (hn6 : ops.pull (lowerHistoryH5) ([2,1,2],[3,1]) false = b1118)
    (hn7 : ops.pull (lowerHistoryH6) ([2,1,2],[3,1]) false = b1098)
    (hn8 : ops.pull (lowerHistoryH7Mixed) ([2,1,2],[3,1]) false = b1088)
    (hn9 : ops.normalization ([2,1,2,3],[3,1]) true true = b395)
    (hn10 : ops.pull (lowerHistoryH7) ([2,1,2,3],[3,1]) true = b753)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,3],[3,1]) true = b1015)
    (hn12 : ops.pull (lowerHistoryHN) ([2,1,2,3],[3,1]) true = b183)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b789,b1118,b1098,b1088,b395,b620,b753,b1015,b183].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b789,b1118,b1098,b1088,b395,b620,b753,b1015,b183]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b789,b1118,b1098,b1088,b395,b620,b753,b1015,b183]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[1]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5]] := by rfl
  have hdone1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced1 : decide (([2],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7Mixed]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps16_61
namespace BindingOps16_62
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b11 : CertBound) (b21 : CertBound) (b43 : CertBound) (b197 : CertBound) (b260 : CertBound) (b272 : CertBound) (b371 : CertBound) (b398 : CertBound) (b440 : CertBound) (b666 : CertBound) (b774 : CertBound) (b786 : CertBound) (b789 : CertBound) (b824 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1047 : CertBound) (b1118 : CertBound)
private def path : LowerHistoryPath := ⟨.left,62,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([2],[]),true)],([1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [b11])
    (hb3 : ops.necessary ⟨⟨([1,2,1,2,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,2,2],[3,1]) = some [b666])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) false = b272)
    (hn4 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (hn5 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) false = b789)
    (hn6 : ops.pull (lowerHistoryH5) ([2,1,2],[3,1]) false = b1118)
    (hn7 : ops.normalization ([2,1,2,2],[3,1]) true true = b398)
    (hn8 : ops.pull (lowerHistoryH7) ([2,1,2,2],[3,1]) true = b786)
    (hn9 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,2],[3,1]) true = b1047)
    (hn10 : ops.pull (lowerHistoryHN) ([2,1,2,2],[3,1]) true = b197)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b789,b1118,b398,b666,b786,b1047,b197].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b789,b1118,b398,b666,b786,b1047,b197]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b789,b1118,b398,b666,b786,b1047,b197]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[1]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5]] := by rfl
  have hdone1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced1 : decide (([2],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps16_62
namespace BindingOps16_63
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b11 : CertBound) (b21 : CertBound) (b43 : CertBound) (b236 : CertBound) (b260 : CertBound) (b272 : CertBound) (b371 : CertBound) (b440 : CertBound) (b747 : CertBound) (b774 : CertBound) (b824 : CertBound) (b829 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1093 : CertBound)
private def path : LowerHistoryPath := ⟨.left,63,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),true)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [b11])
    (hb3 : ops.necessary ⟨⟨([1,2,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,2,1],[3,1]) = some [b747])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) false = b272)
    (hn4 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (hn5 : ops.normalization ([2,1,2,1],[3,1]) true false = b236)
    (hn6 : ops.pull (lowerHistoryH7) ([2,1,2,1],[3,1]) true = b829)
    (hn7 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,1],[3,1]) true = b1093)
    (hn8 : ops.pull (lowerHistoryHN) ([2,1,2,1],[3,1]) true = b236)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b236,b747,b829,b1093,b236].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b236,b747,b829,b1093]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b236,b747,b829,b1093]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[1]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5]] := by rfl
  have hdone1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced1 : decide (([2],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps16_63
namespace BindingOps16_64
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b11 : CertBound) (b21 : CertBound) (b26 : CertBound) (b43 : CertBound) (b203 : CertBound) (b260 : CertBound) (b272 : CertBound) (b371 : CertBound) (b401 : CertBound) (b405 : CertBound) (b440 : CertBound) (b539 : CertBound) (b555 : CertBound) (b643 : CertBound) (b732 : CertBound) (b774 : CertBound) (b824 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b947 : CertBound) (b1002 : CertBound) (b1042 : CertBound)
private def path : LowerHistoryPath := ⟨.left,64,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [b11])
    (hb3 : ops.necessary ⟨⟨([1,2,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,2,1],[3,1]) = some [b26])
    (hb4 : ops.necessary ⟨⟨([1,2,1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,2,1,3],[3,1]) = some [b555])
    (hb5 : ops.necessary ⟨⟨([1,2,1,2,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,2,1,3,1],[3,1]) = some [b539])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) false = b272)
    (hn4 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (hn5 : ops.normalization ([2,1,2,1],[3,1]) false false = b732)
    (hn6 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,1,2,1],[3,1]) false = b1042)
    (hn7 : ops.normalization ([2,1,2,1,3],[3,1]) true true = b405)
    (hn8 : ops.pull (lowerHistoryH2) ([2,1,2,1,3],[3,1]) true = b1002)
    (hn9 : ops.normalization ([2,1,2,1,3,1],[3,1]) true true = b401)
    (hn10 : ops.pull (lowerHistoryH7) ([2,1,2,1,3,1],[3,1]) true = b643)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,1,3,1],[3,1]) true = b947)
    (hn12 : ops.pull (lowerHistoryHN) ([2,1,2,1,3,1],[3,1]) true = b203)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b405,b555,b1002,b401,b539,b643,b947,b203].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b405,b555,b1002,b401,b539,b643,b947,b203]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b405,b555,b1002,b401,b539,b643,b947,b203]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[1]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5]] := by rfl
  have hdone1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced1 : decide (([2],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH7]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice4 : lowerHistorySourceChoices ⟨⟨([1,2,1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hdone4 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced4 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hb5, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, hchoice4, hdone4, hforced4, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps16_64
namespace BindingOps16_65
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b11 : CertBound) (b21 : CertBound) (b26 : CertBound) (b43 : CertBound) (b140 : CertBound) (b182 : CertBound) (b195 : CertBound) (b260 : CertBound) (b272 : CertBound) (b371 : CertBound) (b379 : CertBound) (b388 : CertBound) (b440 : CertBound) (b549 : CertBound) (b568 : CertBound) (b593 : CertBound) (b655 : CertBound) (b672 : CertBound) (b732 : CertBound) (b774 : CertBound) (b824 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b877 : CertBound) (b960 : CertBound) (b1029 : CertBound) (b1042 : CertBound) (b1050 : CertBound)
private def path : LowerHistoryPath := ⟨.left,65,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([2,1,2],[3,1]) = some [b11])
    (hb3 : ops.necessary ⟨⟨([1,2,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,2,1],[3,1]) = some [b26])
    (hb4 : ops.necessary ⟨⟨([1,2,1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,2,1,2],[3,1]) = some [b593])
    (hb5 : ops.necessary ⟨⟨([1,2,1,2,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,2,1,2,1],[3,1]) = some [b549])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1],[3]) false = b272)
    (hn4 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (hn5 : ops.normalization ([2,1,2,1],[3,1]) false false = b732)
    (hn6 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,1,2,1],[3,1]) false = b1042)
    (hn7 : ops.pull (lowerHistoryH7) ([2,1,2,1],[3,1]) false = b195)
    (hn8 : ops.pull (lowerHistoryH9) ([2,1,2,1],[3,1]) false = b877)
    (hn9 : ops.normalization ([2,1,2,1,2],[3,1]) true true = b388)
    (hn10 : ops.pull (lowerHistoryH2) ([2,1,2,1,2],[3,1]) true = b1029)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,2,1,2],[3,1]) true = b182)
    (hn12 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,2,1,2],[3,1]) true = b655)
    (hn13 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1,2,1,2],[3,1]) true = b568)
    (hn14 : ops.pull (lowerHistoryH23) ([2,1,2,1,2],[3,1]) true = b1050)
    (hn15 : ops.normalization ([2,1,2,1,2,1],[3,1]) true true = b379)
    (hn16 : ops.pull (lowerHistoryH7) ([2,1,2,1,2,1],[3,1]) true = b672)
    (hn17 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,1,2,1],[3,1]) true = b960)
    (hn18 : ops.pull (lowerHistoryHN) ([2,1,2,1,2,1],[3,1]) true = b140)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b1029,b379,b549,b672,b960,b140].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140]
] : List (List CertBound))[1])
    (herase2 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b1029,b379,b549,b672,b960,b140].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140]
] : List (List CertBound))[2])
    (herase3 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140]
] : List (List CertBound))[3])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b1042,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b1029,b379,b549,b672,b960,b140],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b272,b774,b11,b732,b26,b195,b877,b388,b593,b182,b655,b568,b1050,b379,b549,b672,b960,b140]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[1]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5]] := by rfl
  have hdone1 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced1 : decide (([2],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (false,([2],[1]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,2,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice4 : lowerHistorySourceChoices ⟨⟨([1,2,1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone4 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced4 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hb5, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, hchoice4, hdone4, hforced4, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1, herase2, herase3]
  rfl
end BindingOps16_65

open Freiman

private def sourceBound3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩

private def sourceBound11 : CertBound := ⟨true,false,⟨⟨(-5111577/15657181),(3840568/15657181),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def sourceBound21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def sourceBound26 : CertBound := ⟨true,false,⟨⟨(-25544163/190658063),(19094857/190658063),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def sourceBound43 : CertBound := ⟨true,false,⟨⟨(-27041/364702),(168601/1094106),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def sourceBound140 : CertBound := ⟨true,false,⟨⟨(11731/1422118),0,0,(433/1422118)⟩,⟨(109/302),0,0,(1/906)⟩,⟨(3453/9418),0,0,(-1/9418)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound182 : CertBound := ⟨true,false,⟨⟨(416400055300/14271340563181),(2655398800/14271340563181),0,0⟩,⟨(38250/104497),(-1/104497),0,0⟩,⟨(103957/283933),(1/283933),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound183 : CertBound := ⟨true,false,⟨⟨(3211/109150),0,0,(49/109150)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound195 : CertBound := ⟨true,false,⟨⟨(194269963/5454255300),(2189251/218170212),0,0⟩,⟨(439/1202),(1/3606),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound197 : CertBound := ⟨true,false,⟨⟨(1671/46166),0,0,(1475/323162)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound203 : CertBound := ⟨true,false,⟨⟨(75/1747),0,0,(-496/61145)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(6391/17470),0,0,(-1/17470)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound236 : CertBound := ⟨true,false,⟨⟨(15/134),0,0,(23/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound260 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private def sourceBound272 : CertBound := ⟨true,false,⟨⟨(33285470319/67820291500),(-327225429/33910145750),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def sourceBound371 : CertBound := ⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

private def sourceBound379 : CertBound := ⟨true,true,⟨⟨(11731/1422118),0,0,(433/1422118)⟩,⟨(109/302),0,0,(1/906)⟩,⟨(3453/9418),0,0,(-1/9418)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound388 : CertBound := ⟨true,true,⟨⟨(551/34277),0,0,(414/239939)⟩,⟨(109/302),0,0,(1/906)⟩,⟨(167/454),0,0,(-1/3178)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound395 : CertBound := ⟨true,true,⟨⟨(3211/109150),0,0,(49/109150)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound398 : CertBound := ⟨true,true,⟨⟨(1671/46166),0,0,(1475/323162)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound401 : CertBound := ⟨true,true,⟨⟨(75/1747),0,0,(-496/61145)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(6391/17470),0,0,(-1/17470)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound405 : CertBound := ⟨true,true,⟨⟨(1689/35690),0,0,(-1817/249830)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(2615/7138),0,0,(-1/7138)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private def sourceBound539 : CertBound := ⟨false,false,⟨⟨(295645379/34737062867),(221489974/34737062867),0,0⟩,⟨(63631/174094),(-1/174094),0,0⟩,⟨(11220/30697),(1/30697),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound549 : CertBound := ⟨false,false,⟨⟨(231057/22960561),(1270246/68881683),0,0⟩,⟨(2241/6122),(1/18366),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound555 : CertBound := ⟨false,false,⟨⟨(7185630/680098211),(52919348/2040294633),0,0⟩,⟨(439/1202),(1/3606),0,0⟩,⟨(63631/174094),(-1/174094),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound568 : CertBound := ⟨false,false,⟨⟨(17496401/1450108957),(201423059/17401307484),0,0⟩,⟨(2241/6122),(1/18366),0,0⟩,⟨(173564/473737),(-1/473737),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound593 : CertBound := ⟨false,false,⟨⟨(312097/17559841),(879473/17559841),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound620 : CertBound := ⟨false,false,⟨⟨(42724568/1681253509),(96584076/1681253509),0,0⟩,⟨(28970/78049),(1/78049),0,0⟩,⟨(616/1657),(-1/1657),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound643 : CertBound := ⟨false,false,⟨⟨(7353418800/256083887081),(-6298235450/768251661243),0,0⟩,⟨(6565/17963),(1/53889),0,0⟩,⟨(30565/83614),(-1/83614),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound655 : CertBound := ⟨false,false,⟨⟨(7584289377500/205055504298333),(166270436500/205055504298333),0,0⟩,⟨(103957/283933),(1/283933),0,0⟩,⟨(5298/14461),(-1/14461),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private def sourceBound666 : CertBound := ⟨false,false,⟨⟨(972280/21096959),(2470191/21096959),0,0⟩,⟨(1161/3142),(1/3142),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound672 : CertBound := ⟨false,false,⟨⟨(26349523850/548964322709),(-7502818050/548964322709),0,0⟩,⟨(11929/32593),(1/32593),0,0⟩,⟨(18084/49393),(-1/49393),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound732 : CertBound := ⟨false,false,⟨⟨(15/134),0,0,(23/4690)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(251/670),0,0,(-1/670)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound747 : CertBound := ⟨false,false,⟨⟨(214600/1533493),(1183231/4600479),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound753 : CertBound := ⟨false,false,⟨⟨(2709504850/17611227007),(-2273395150/52833681021),0,0⟩,⟨(4178/11269),(1/11269),0,0⟩,⟨(1701/4583),(-1/13749),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound774 : CertBound := ⟨false,false,⟨⟨(41/185),0,0,(32/1295)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound786 : CertBound := ⟨false,false,⟨⟨(114542650/408037531),(-96533350/1224112593),0,0⟩,⟨(735/1991),(1/5973),0,0⟩,⟨(2890/7813),(-1/7813),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound789 : CertBound := ⟨false,false,⟨⟨(154748703689/531731481700),(100050183/265865740850),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩

private def sourceBound824 : CertBound := ⟨false,false,⟨⟨(3418287291/5478244850),(-26216794/8217367275),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩

private def sourceBound829 : CertBound := ⟨false,false,⟨⟨(1890656950/2826713021),(-538238350/2826713021),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound833 : CertBound := ⟨false,false,⟨⟨(7/10),0,0,(1/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def sourceBound843 : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩

private def sourceBound856 : CertBound := ⟨false,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def sourceBound877 : CertBound := ⟨false,false,⟨⟨(1186584/30433),(-683411/30433),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound947 : CertBound := ⟨false,true,⟨⟨(18283513/4505874846),(10652047/4505874846),0,0⟩,⟨(6565/17963),(1/53889),0,0⟩,⟨(30565/83614),(-1/83614),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound960 : CertBound := ⟨false,true,⟨⟨(10947811/1609866049),(19134112/4829598147),0,0⟩,⟨(11929/32593),(1/32593),0,0⟩,⟨(18084/49393),(-1/49393),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1002 : CertBound := ⟨false,true,⟨⟨(1516196471650/87327732407149),(31597917350/261983197221447),0,0⟩,⟨(63631/174094),(-1/174094),0,0⟩,⟨(58649/160439),(1/481317),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1015 : CertBound := ⟨false,true,⟨⟨(3436033/154937481),(667124/51645827),0,0⟩,⟨(4178/11269),(1/11269),0,0⟩,⟨(1701/4583),(-1/13749),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1029 : CertBound := ⟨false,true,⟨⟨(416400055300/14271340563181),(2655398800/14271340563181),0,0⟩,⟨(38250/104497),(-1/104497),0,0⟩,⟨(103957/283933),(1/283933),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1042 : CertBound := ⟨false,true,⟨⟨(194269963/5454255300),(2189251/218170212),0,0⟩,⟨(439/1202),(1/3606),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1047 : CertBound := ⟨false,true,⟨⟨(1880401/46667049),(365108/15555683),0,0⟩,⟨(735/1991),(1/5973),0,0⟩,⟨(2890/7813),(-1/7813),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1050 : CertBound := ⟨false,true,⟨⟨(12332455500/296039619187),(-509955500/296039619187),0,0⟩,⟨(103957/283933),(1/283933),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1088 : CertBound := ⟨false,true,⟨⟨(3187478/35004125),(1328733/70008250),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(616/1657),(-1/1657),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1093 : CertBound := ⟨false,true,⟨⟨(785697/8289481),(1373204/24868443),0,0⟩,⟨(856/2341),(1/2341),0,0⟩,⟨(1301/3541),(-1/3541),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1098 : CertBound := ⟨false,true,⟨⟨(1641924483/15716862500),0,0,(246790851/31433725000)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(3913/10550),0,0,(-1/31650)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def sourceBound1118 : CertBound := ⟨false,true,⟨⟨(12740018571/65624465320),(6136962399/1640611633000),0,0⟩,⟨(5491/14843),(1/44529),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman
namespace SourceMemo16_61
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,61,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([3],[]),true)],([1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound789,sourceBound1118,sourceBound1098,sourceBound1088,sourceBound395,sourceBound620,sourceBound753,sourceBound1015,sourceBound183]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound789,sourceBound1118,sourceBound1098,sourceBound1088,sourceBound395,sourceBound620,sourceBound753,sourceBound1015,sourceBound183].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_61.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b11 := sourceBound11) (b21 := sourceBound21) (b43 := sourceBound43) (b183 := sourceBound183) (b260 := sourceBound260) (b272 := sourceBound272) (b371 := sourceBound371) (b395 := sourceBound395) (b440 := sourceBound440) (b620 := sourceBound620) (b753 := sourceBound753) (b774 := sourceBound774) (b789 := sourceBound789) (b824 := sourceBound824) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b1015 := sourceBound1015) (b1088 := sourceBound1088) (b1098 := sourceBound1098) (b1118 := sourceBound1118)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG2.2.2.2.2.2.2.1) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pull16 BindingNumeric16.norm21 BindingNumeric16.pullKey52 BindingNumeric16.pullKey53 BindingNumeric16.pullKey54 BindingNumeric16.pullKey55 BindingNumeric16.norm22 BindingNumeric16.pullKey56 BindingNumeric16.pullKey57 BindingNumeric16.pullKey58 eraseActual0)
end SourceMemo16_61

open Freiman
open Freiman
namespace SourceMemo16_62
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,62,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([2],[]),true)],([1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound789,sourceBound1118,sourceBound398,sourceBound666,sourceBound786,sourceBound1047,sourceBound197]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound789,sourceBound1118,sourceBound398,sourceBound666,sourceBound786,sourceBound1047,sourceBound197].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_62.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b11 := sourceBound11) (b21 := sourceBound21) (b43 := sourceBound43) (b197 := sourceBound197) (b260 := sourceBound260) (b272 := sourceBound272) (b371 := sourceBound371) (b398 := sourceBound398) (b440 := sourceBound440) (b666 := sourceBound666) (b774 := sourceBound774) (b786 := sourceBound786) (b789 := sourceBound789) (b824 := sourceBound824) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b1047 := sourceBound1047) (b1118 := sourceBound1118)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG2.2.2.2.2.2.2.2) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pull16 BindingNumeric16.norm21 BindingNumeric16.pullKey52 BindingNumeric16.pullKey53 BindingNumeric16.norm23 BindingNumeric16.pullKey59 BindingNumeric16.pullKey60 BindingNumeric16.pullKey61 eraseActual0)
end SourceMemo16_62

open Freiman
open Freiman
namespace SourceMemo16_63
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,63,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),true)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound236,sourceBound747,sourceBound829,sourceBound1093]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : ([sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound236,sourceBound747,sourceBound829,sourceBound1093] ++ [sourceBound236]).eraseDups = expected[0] := by
  have hdup : sourceBound236 ∈ expected[0] := by simp [expected]
  change (expected[0] ++ [sourceBound236]).eraseDups = expected[0]
  rw [List.eraseDups_append, erase0,
    BindingSourceSupport16.singleton_removeAll_of_mem hdup,
    List.eraseDups_nil, List.append_nil]
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_63.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b11 := sourceBound11) (b21 := sourceBound21) (b43 := sourceBound43) (b236 := sourceBound236) (b260 := sourceBound260) (b272 := sourceBound272) (b371 := sourceBound371) (b440 := sourceBound440) (b747 := sourceBound747) (b774 := sourceBound774) (b824 := sourceBound824) (b829 := sourceBound829) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b1093 := sourceBound1093)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG3.1) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pull16 BindingNumeric16.norm21 BindingNumeric16.norm24 BindingNumeric16.pullKey49 BindingNumeric16.pullKey50 BindingNumeric16.pullKey51 eraseActual0)
end SourceMemo16_63

open Freiman
open Freiman
namespace SourceMemo16_64
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,64,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound1042,sourceBound405,sourceBound555,sourceBound1002,sourceBound401,sourceBound539,sourceBound643,sourceBound947,sourceBound203]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound1042,sourceBound405,sourceBound555,sourceBound1002,sourceBound401,sourceBound539,sourceBound643,sourceBound947,sourceBound203].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_64.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b11 := sourceBound11) (b21 := sourceBound21) (b26 := sourceBound26) (b43 := sourceBound43) (b203 := sourceBound203) (b260 := sourceBound260) (b272 := sourceBound272) (b371 := sourceBound371) (b401 := sourceBound401) (b405 := sourceBound405) (b440 := sourceBound440) (b539 := sourceBound539) (b555 := sourceBound555) (b643 := sourceBound643) (b732 := sourceBound732) (b774 := sourceBound774) (b824 := sourceBound824) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b947 := sourceBound947) (b1002 := sourceBound1002) (b1042 := sourceBound1042)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG3.2.1) (BindingSourceBranches16.branchesG3.2.2.1) (BindingSourceBranches16.branchesG3.2.2.2.1) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pull16 BindingNumeric16.norm21 BindingNumeric16.norm25 BindingNumeric16.pull68 BindingNumeric16.norm26 BindingNumeric16.pullKey63 BindingNumeric16.norm27 BindingNumeric16.pullKey64 BindingNumeric16.pullKey65 BindingNumeric16.pullKey66 eraseActual0)
end SourceMemo16_64

open Freiman
open Freiman
namespace SourceMemo16_65
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,65,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound1042,sourceBound388,sourceBound593,sourceBound1029,sourceBound379,sourceBound549,sourceBound672,sourceBound960,sourceBound140],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound1042,sourceBound388,sourceBound593,sourceBound182,sourceBound655,sourceBound568,sourceBound1050,sourceBound379,sourceBound549,sourceBound672,sourceBound960,sourceBound140],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound195,sourceBound877,sourceBound388,sourceBound593,sourceBound1029,sourceBound379,sourceBound549,sourceBound672,sourceBound960,sourceBound140],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound195,sourceBound877,sourceBound388,sourceBound593,sourceBound182,sourceBound655,sourceBound568,sourceBound1050,sourceBound379,sourceBound549,sourceBound672,sourceBound960,sourceBound140]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound1042,sourceBound388,sourceBound593,sourceBound1029,sourceBound379,sourceBound549,sourceBound672,sourceBound960,sourceBound140].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound1042,sourceBound388,sourceBound593,sourceBound182,sourceBound655,sourceBound568,sourceBound1050,sourceBound379,sourceBound549,sourceBound672,sourceBound960,sourceBound140].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem erase2 : expected[2].eraseDups = expected[2] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[2] (by simp [expected])))
private theorem eraseActual2 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound195,sourceBound877,sourceBound388,sourceBound593,sourceBound1029,sourceBound379,sourceBound549,sourceBound672,sourceBound960,sourceBound140].eraseDups = expected[2] := by
  simpa [expected] using erase2
private theorem erase3 : expected[3].eraseDups = expected[3] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[3] (by simp [expected])))
private theorem eraseActual3 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound272,sourceBound774,sourceBound11,sourceBound732,sourceBound26,sourceBound195,sourceBound877,sourceBound388,sourceBound593,sourceBound182,sourceBound655,sourceBound568,sourceBound1050,sourceBound379,sourceBound549,sourceBound672,sourceBound960,sourceBound140].eraseDups = expected[3] := by
  simpa [expected] using erase3
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_65.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b11 := sourceBound11) (b21 := sourceBound21) (b26 := sourceBound26) (b43 := sourceBound43) (b140 := sourceBound140) (b182 := sourceBound182) (b195 := sourceBound195) (b260 := sourceBound260) (b272 := sourceBound272) (b371 := sourceBound371) (b379 := sourceBound379) (b388 := sourceBound388) (b440 := sourceBound440) (b549 := sourceBound549) (b568 := sourceBound568) (b593 := sourceBound593) (b655 := sourceBound655) (b672 := sourceBound672) (b732 := sourceBound732) (b774 := sourceBound774) (b824 := sourceBound824) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b877 := sourceBound877) (b960 := sourceBound960) (b1029 := sourceBound1029) (b1042 := sourceBound1042) (b1050 := sourceBound1050)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG3.2.1) (BindingSourceBranches16.branchesG3.2.2.2.2.1) (BindingSourceBranches16.branchesG3.2.2.2.2.2.1) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pull16 BindingNumeric16.norm21 BindingNumeric16.norm25 BindingNumeric16.pull68 BindingNumeric16.pullKey62 BindingNumeric16.pullKey67 BindingNumeric16.norm28 BindingNumeric16.pullKey68 BindingNumeric16.pull76 BindingNumeric16.pullKey69 BindingNumeric16.pullKey70 BindingNumeric16.pullKey71 BindingNumeric16.norm29 BindingNumeric16.pullKey72 BindingNumeric16.pullKey73 BindingNumeric16.pullKey74 eraseActual0 eraseActual1 eraseActual2 eraseActual3)
end SourceMemo16_65

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman


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
private def path61 : LowerHistoryPath := ⟨.left,61,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([3],[]),true)],([1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩

private theorem records61 : lowerHistoryRecordsFor path61 = [⟨.left,61,0,(-1),false,325,907⟩] := by
  change lowerHistoryRecordsFor (⟨.left,61,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 61, lowerHistoryRecordsL_list] <;> rfl


private def path62 : LowerHistoryPath := ⟨.left,62,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([2],[]),true)],([1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩

private theorem records62 : lowerHistoryRecordsFor path62 = [⟨.left,62,0,(-1),false,327,949⟩] := by
  change lowerHistoryRecordsFor (⟨.left,62,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 62, lowerHistoryRecordsL_list] <;> rfl


private def path63 : LowerHistoryPath := ⟨.left,63,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),true)],([1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩

private theorem records63 : lowerHistoryRecordsFor path63 = [⟨.left,63,0,(-1),false,329,997⟩] := by
  change lowerHistoryRecordsFor (⟨.left,63,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 63, lowerHistoryRecordsL_list] <;> rfl


private def path64 : LowerHistoryPath := ⟨.left,64,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([3],[]),true),(([],[1]),false)],([1,2,1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩

private theorem records64 : lowerHistoryRecordsFor path64 = [⟨.left,64,0,(-1),false,323,841⟩] := by
  change lowerHistoryRecordsFor (⟨.left,64,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 64, lowerHistoryRecordsL_list] <;> rfl


private def path65 : LowerHistoryPath := ⟨.left,65,[1],([2],[3]),false,[(([1],[]),false),(([2],[1]),false),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,2,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩

private theorem records65 : lowerHistoryRecordsFor path65 = [⟨.left,65,0,(-1),false,307,853⟩,⟨.left,65,1,(-1),false,303,853⟩,⟨.left,65,2,(-1),false,305,853⟩,⟨.left,65,3,(-1),false,301,853⟩] := by
  change lowerHistoryRecordsFor (⟨.left,65,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 65, lowerHistoryRecordsL_list] <;> rfl


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

private theorem bound260 :
    lowerHistoryBound 260 = sourceBound260 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[59]? = some sourceBound260 :=
    Eq.refl (some sourceBound260)
  exact (BoundCompact16.global_to_chunk2 59 (by decide)).trans hlocal

private theorem bound371 :
    lowerHistoryBound 371 = sourceBound371 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[170]? = some sourceBound371 :=
    Eq.refl (some sourceBound371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hlocal

private theorem bound440 :
    lowerHistoryBound 440 = sourceBound440 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[39]? = some sourceBound440 :=
    Eq.refl (some sourceBound440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hlocal

private theorem bound747 :
    lowerHistoryBound 747 = sourceBound747 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[146]? = some sourceBound747 :=
    Eq.refl (some sourceBound747)
  exact (BoundCompact16.global_to_chunk4 146 (by decide)).trans hlocal

private theorem bound829 :
    lowerHistoryBound 829 = sourceBound829 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[28]? = some sourceBound829 :=
    Eq.refl (some sourceBound829)
  exact (BoundCompact16.global_to_chunk5 28 (by decide)).trans hlocal

private theorem bound843 :
    lowerHistoryBound 843 = sourceBound843 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[42]? = some sourceBound843 :=
    Eq.refl (some sourceBound843)
  exact (BoundCompact16.global_to_chunk5 42 (by decide)).trans hlocal

private theorem bound856 :
    lowerHistoryBound 856 = sourceBound856 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[55]? = some sourceBound856 :=
    Eq.refl (some sourceBound856)
  exact (BoundCompact16.global_to_chunk5 55 (by decide)).trans hlocal

private theorem bound1093 :
    lowerHistoryBound 1093 = sourceBound1093 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[92]? = some sourceBound1093 :=
    Eq.refl (some sourceBound1093)
  exact (BoundCompact16.global_to_chunk6 92).trans hlocal

end BatchLookup15

namespace BatchLookup16
open Freiman

private theorem bound11 :
    lowerHistoryBound 11 = sourceBound11 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[10]? = some sourceBound11 :=
    Eq.refl (some sourceBound11)
  exact (BoundCompact16.global_to_chunk1 10 (by decide)).trans hlocal

private theorem bound26 :
    lowerHistoryBound 26 = sourceBound26 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[25]? = some sourceBound26 :=
    Eq.refl (some sourceBound26)
  exact (BoundCompact16.global_to_chunk1 25 (by decide)).trans hlocal

private theorem bound43 :
    lowerHistoryBound 43 = sourceBound43 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[42]? = some sourceBound43 :=
    Eq.refl (some sourceBound43)
  exact (BoundCompact16.global_to_chunk1 42 (by decide)).trans hlocal

private theorem bound140 :
    lowerHistoryBound 140 = sourceBound140 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[139]? = some sourceBound140 :=
    Eq.refl (some sourceBound140)
  exact (BoundCompact16.global_to_chunk1 139 (by decide)).trans hlocal

private theorem bound182 :
    lowerHistoryBound 182 = sourceBound182 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[181]? = some sourceBound182 :=
    Eq.refl (some sourceBound182)
  exact (BoundCompact16.global_to_chunk1 181 (by decide)).trans hlocal

private theorem bound183 :
    lowerHistoryBound 183 = sourceBound183 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[182]? = some sourceBound183 :=
    Eq.refl (some sourceBound183)
  exact (BoundCompact16.global_to_chunk1 182 (by decide)).trans hlocal

private theorem bound195 :
    lowerHistoryBound 195 = sourceBound195 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[194]? = some sourceBound195 :=
    Eq.refl (some sourceBound195)
  exact (BoundCompact16.global_to_chunk1 194 (by decide)).trans hlocal

private theorem bound197 :
    lowerHistoryBound 197 = sourceBound197 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[196]? = some sourceBound197 :=
    Eq.refl (some sourceBound197)
  exact (BoundCompact16.global_to_chunk1 196 (by decide)).trans hlocal

private theorem bound203 :
    lowerHistoryBound 203 = sourceBound203 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[2]? = some sourceBound203 :=
    Eq.refl (some sourceBound203)
  exact (BoundCompact16.global_to_chunk2 2 (by decide)).trans hlocal

private theorem bound272 :
    lowerHistoryBound 272 = sourceBound272 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[71]? = some sourceBound272 :=
    Eq.refl (some sourceBound272)
  exact (BoundCompact16.global_to_chunk2 71 (by decide)).trans hlocal

private theorem bound379 :
    lowerHistoryBound 379 = sourceBound379 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[178]? = some sourceBound379 :=
    Eq.refl (some sourceBound379)
  exact (BoundCompact16.global_to_chunk2 178 (by decide)).trans hlocal

private theorem bound388 :
    lowerHistoryBound 388 = sourceBound388 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[187]? = some sourceBound388 :=
    Eq.refl (some sourceBound388)
  exact (BoundCompact16.global_to_chunk2 187 (by decide)).trans hlocal

private theorem bound395 :
    lowerHistoryBound 395 = sourceBound395 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[194]? = some sourceBound395 :=
    Eq.refl (some sourceBound395)
  exact (BoundCompact16.global_to_chunk2 194 (by decide)).trans hlocal

private theorem bound398 :
    lowerHistoryBound 398 = sourceBound398 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[197]? = some sourceBound398 :=
    Eq.refl (some sourceBound398)
  exact (BoundCompact16.global_to_chunk2 197 (by decide)).trans hlocal

private theorem bound401 :
    lowerHistoryBound 401 = sourceBound401 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[0]? = some sourceBound401 :=
    Eq.refl (some sourceBound401)
  exact (BoundCompact16.global_to_chunk3 0 (by decide)).trans hlocal

private theorem bound405 :
    lowerHistoryBound 405 = sourceBound405 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[4]? = some sourceBound405 :=
    Eq.refl (some sourceBound405)
  exact (BoundCompact16.global_to_chunk3 4 (by decide)).trans hlocal

private theorem bound539 :
    lowerHistoryBound 539 = sourceBound539 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[138]? = some sourceBound539 :=
    Eq.refl (some sourceBound539)
  exact (BoundCompact16.global_to_chunk3 138 (by decide)).trans hlocal

private theorem bound549 :
    lowerHistoryBound 549 = sourceBound549 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[148]? = some sourceBound549 :=
    Eq.refl (some sourceBound549)
  exact (BoundCompact16.global_to_chunk3 148 (by decide)).trans hlocal

private theorem bound555 :
    lowerHistoryBound 555 = sourceBound555 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[154]? = some sourceBound555 :=
    Eq.refl (some sourceBound555)
  exact (BoundCompact16.global_to_chunk3 154 (by decide)).trans hlocal

private theorem bound568 :
    lowerHistoryBound 568 = sourceBound568 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[167]? = some sourceBound568 :=
    Eq.refl (some sourceBound568)
  exact (BoundCompact16.global_to_chunk3 167 (by decide)).trans hlocal

private theorem bound593 :
    lowerHistoryBound 593 = sourceBound593 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[192]? = some sourceBound593 :=
    Eq.refl (some sourceBound593)
  exact (BoundCompact16.global_to_chunk3 192 (by decide)).trans hlocal

private theorem bound620 :
    lowerHistoryBound 620 = sourceBound620 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[19]? = some sourceBound620 :=
    Eq.refl (some sourceBound620)
  exact (BoundCompact16.global_to_chunk4 19 (by decide)).trans hlocal

private theorem bound643 :
    lowerHistoryBound 643 = sourceBound643 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[42]? = some sourceBound643 :=
    Eq.refl (some sourceBound643)
  exact (BoundCompact16.global_to_chunk4 42 (by decide)).trans hlocal

private theorem bound655 :
    lowerHistoryBound 655 = sourceBound655 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[54]? = some sourceBound655 :=
    Eq.refl (some sourceBound655)
  exact (BoundCompact16.global_to_chunk4 54 (by decide)).trans hlocal

private theorem bound666 :
    lowerHistoryBound 666 = sourceBound666 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[65]? = some sourceBound666 :=
    Eq.refl (some sourceBound666)
  exact (BoundCompact16.global_to_chunk4 65 (by decide)).trans hlocal

private theorem bound672 :
    lowerHistoryBound 672 = sourceBound672 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[71]? = some sourceBound672 :=
    Eq.refl (some sourceBound672)
  exact (BoundCompact16.global_to_chunk4 71 (by decide)).trans hlocal

private theorem bound732 :
    lowerHistoryBound 732 = sourceBound732 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[131]? = some sourceBound732 :=
    Eq.refl (some sourceBound732)
  exact (BoundCompact16.global_to_chunk4 131 (by decide)).trans hlocal

private theorem bound753 :
    lowerHistoryBound 753 = sourceBound753 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[152]? = some sourceBound753 :=
    Eq.refl (some sourceBound753)
  exact (BoundCompact16.global_to_chunk4 152 (by decide)).trans hlocal

private theorem bound774 :
    lowerHistoryBound 774 = sourceBound774 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[173]? = some sourceBound774 :=
    Eq.refl (some sourceBound774)
  exact (BoundCompact16.global_to_chunk4 173 (by decide)).trans hlocal

private theorem bound786 :
    lowerHistoryBound 786 = sourceBound786 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[185]? = some sourceBound786 :=
    Eq.refl (some sourceBound786)
  exact (BoundCompact16.global_to_chunk4 185 (by decide)).trans hlocal

private theorem bound789 :
    lowerHistoryBound 789 = sourceBound789 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[188]? = some sourceBound789 :=
    Eq.refl (some sourceBound789)
  exact (BoundCompact16.global_to_chunk4 188 (by decide)).trans hlocal

private theorem bound824 :
    lowerHistoryBound 824 = sourceBound824 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[23]? = some sourceBound824 :=
    Eq.refl (some sourceBound824)
  exact (BoundCompact16.global_to_chunk5 23 (by decide)).trans hlocal

private theorem bound833 :
    lowerHistoryBound 833 = sourceBound833 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[32]? = some sourceBound833 :=
    Eq.refl (some sourceBound833)
  exact (BoundCompact16.global_to_chunk5 32 (by decide)).trans hlocal

private theorem bound877 :
    lowerHistoryBound 877 = sourceBound877 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[76]? = some sourceBound877 :=
    Eq.refl (some sourceBound877)
  exact (BoundCompact16.global_to_chunk5 76 (by decide)).trans hlocal

private theorem bound947 :
    lowerHistoryBound 947 = sourceBound947 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[146]? = some sourceBound947 :=
    Eq.refl (some sourceBound947)
  exact (BoundCompact16.global_to_chunk5 146 (by decide)).trans hlocal

private theorem bound960 :
    lowerHistoryBound 960 = sourceBound960 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[159]? = some sourceBound960 :=
    Eq.refl (some sourceBound960)
  exact (BoundCompact16.global_to_chunk5 159 (by decide)).trans hlocal

private theorem bound1002 :
    lowerHistoryBound 1002 = sourceBound1002 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[1]? = some sourceBound1002 :=
    Eq.refl (some sourceBound1002)
  exact (BoundCompact16.global_to_chunk6 1).trans hlocal

private theorem bound1015 :
    lowerHistoryBound 1015 = sourceBound1015 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[14]? = some sourceBound1015 :=
    Eq.refl (some sourceBound1015)
  exact (BoundCompact16.global_to_chunk6 14).trans hlocal

private theorem bound1029 :
    lowerHistoryBound 1029 = sourceBound1029 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[28]? = some sourceBound1029 :=
    Eq.refl (some sourceBound1029)
  exact (BoundCompact16.global_to_chunk6 28).trans hlocal

private theorem bound1042 :
    lowerHistoryBound 1042 = sourceBound1042 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[41]? = some sourceBound1042 :=
    Eq.refl (some sourceBound1042)
  exact (BoundCompact16.global_to_chunk6 41).trans hlocal

private theorem bound1047 :
    lowerHistoryBound 1047 = sourceBound1047 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[46]? = some sourceBound1047 :=
    Eq.refl (some sourceBound1047)
  exact (BoundCompact16.global_to_chunk6 46).trans hlocal

private theorem bound1050 :
    lowerHistoryBound 1050 = sourceBound1050 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[49]? = some sourceBound1050 :=
    Eq.refl (some sourceBound1050)
  exact (BoundCompact16.global_to_chunk6 49).trans hlocal

private theorem bound1088 :
    lowerHistoryBound 1088 = sourceBound1088 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[87]? = some sourceBound1088 :=
    Eq.refl (some sourceBound1088)
  exact (BoundCompact16.global_to_chunk6 87).trans hlocal

private theorem bound1098 :
    lowerHistoryBound 1098 = sourceBound1098 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[97]? = some sourceBound1098 :=
    Eq.refl (some sourceBound1098)
  exact (BoundCompact16.global_to_chunk6 97).trans hlocal

private theorem bound1118 :
    lowerHistoryBound 1118 = sourceBound1118 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[117]? = some sourceBound1118 :=
    Eq.refl (some sourceBound1118)
  exact (BoundCompact16.global_to_chunk6 117).trans hlocal

end BatchLookup16


-- Source: agents.batch16.SourceValuesAll
open Freiman
namespace SourceValues16
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem source61 : lowerHistorySourcePremises BatchLookup16.path61 =
    ([[371,843,260,440,3,856,21,833,43,824,272,774,11,789,1118,1098,1088,395,620,753,1015,183]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound272 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup16.bound789 (congrArg₂ List.cons BatchLookup16.bound1118 (congrArg₂ List.cons BatchLookup16.bound1098 (congrArg₂ List.cons BatchLookup16.bound1088 (congrArg₂ List.cons BatchLookup16.bound395 (congrArg₂ List.cons BatchLookup16.bound620 (congrArg₂ List.cons BatchLookup16.bound753 (congrArg₂ List.cons BatchLookup16.bound1015 (congrArg₂ List.cons BatchLookup16.bound183 (rfl : ([] : List CertBound) = []))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo16_61.source.trans hb.symm
private theorem length61 : BatchLookup16.path61.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path61).length := by
  exact (congrArg List.length source61).symm
private theorem source62 : lowerHistorySourcePremises BatchLookup16.path62 =
    ([[371,843,260,440,3,856,21,833,43,824,272,774,11,789,1118,398,666,786,1047,197]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound272 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup16.bound789 (congrArg₂ List.cons BatchLookup16.bound1118 (congrArg₂ List.cons BatchLookup16.bound398 (congrArg₂ List.cons BatchLookup16.bound666 (congrArg₂ List.cons BatchLookup16.bound786 (congrArg₂ List.cons BatchLookup16.bound1047 (congrArg₂ List.cons BatchLookup16.bound197 (rfl : ([] : List CertBound) = []))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo16_62.source.trans hb.symm
private theorem length62 : BatchLookup16.path62.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path62).length := by
  exact (congrArg List.length source62).symm
private theorem source63 : lowerHistorySourcePremises BatchLookup16.path63 =
    ([[371,843,260,440,3,856,21,833,43,824,272,774,11,236,747,829,1093]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound272 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup15.bound236 (congrArg₂ List.cons BatchLookup15.bound747 (congrArg₂ List.cons BatchLookup15.bound829 (congrArg₂ List.cons BatchLookup15.bound1093 (rfl : ([] : List CertBound) = [])))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo16_63.source.trans hb.symm
private theorem length63 : BatchLookup16.path63.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path63).length := by
  exact (congrArg List.length source63).symm
private theorem source64 : lowerHistorySourcePremises BatchLookup16.path64 =
    ([[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,1042,405,555,1002,401,539,643,947,203]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound272 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup16.bound732 (congrArg₂ List.cons BatchLookup16.bound26 (congrArg₂ List.cons BatchLookup16.bound1042 (congrArg₂ List.cons BatchLookup16.bound405 (congrArg₂ List.cons BatchLookup16.bound555 (congrArg₂ List.cons BatchLookup16.bound1002 (congrArg₂ List.cons BatchLookup16.bound401 (congrArg₂ List.cons BatchLookup16.bound539 (congrArg₂ List.cons BatchLookup16.bound643 (congrArg₂ List.cons BatchLookup16.bound947 (congrArg₂ List.cons BatchLookup16.bound203 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo16_64.source.trans hb.symm
private theorem length64 : BatchLookup16.path64.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path64).length := by
  exact (congrArg List.length source64).symm
private theorem source65 : lowerHistorySourcePremises BatchLookup16.path65 =
    ([[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,1042,388,593,1029,379,549,672,960,140],[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,1042,388,593,182,655,568,1050,379,549,672,960,140],[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,195,877,388,593,1029,379,549,672,960,140],[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,195,877,388,593,182,655,568,1050,379,549,672,960,140]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound272 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup16.bound732 (congrArg₂ List.cons BatchLookup16.bound26 (congrArg₂ List.cons BatchLookup16.bound1042 (congrArg₂ List.cons BatchLookup16.bound388 (congrArg₂ List.cons BatchLookup16.bound593 (congrArg₂ List.cons BatchLookup16.bound1029 (congrArg₂ List.cons BatchLookup16.bound379 (congrArg₂ List.cons BatchLookup16.bound549 (congrArg₂ List.cons BatchLookup16.bound672 (congrArg₂ List.cons BatchLookup16.bound960 (congrArg₂ List.cons BatchLookup16.bound140 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound272 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup16.bound732 (congrArg₂ List.cons BatchLookup16.bound26 (congrArg₂ List.cons BatchLookup16.bound1042 (congrArg₂ List.cons BatchLookup16.bound388 (congrArg₂ List.cons BatchLookup16.bound593 (congrArg₂ List.cons BatchLookup16.bound182 (congrArg₂ List.cons BatchLookup16.bound655 (congrArg₂ List.cons BatchLookup16.bound568 (congrArg₂ List.cons BatchLookup16.bound1050 (congrArg₂ List.cons BatchLookup16.bound379 (congrArg₂ List.cons BatchLookup16.bound549 (congrArg₂ List.cons BatchLookup16.bound672 (congrArg₂ List.cons BatchLookup16.bound960 (congrArg₂ List.cons BatchLookup16.bound140 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound272 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup16.bound732 (congrArg₂ List.cons BatchLookup16.bound26 (congrArg₂ List.cons BatchLookup16.bound195 (congrArg₂ List.cons BatchLookup16.bound877 (congrArg₂ List.cons BatchLookup16.bound388 (congrArg₂ List.cons BatchLookup16.bound593 (congrArg₂ List.cons BatchLookup16.bound1029 (congrArg₂ List.cons BatchLookup16.bound379 (congrArg₂ List.cons BatchLookup16.bound549 (congrArg₂ List.cons BatchLookup16.bound672 (congrArg₂ List.cons BatchLookup16.bound960 (congrArg₂ List.cons BatchLookup16.bound140 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound272 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup16.bound732 (congrArg₂ List.cons BatchLookup16.bound26 (congrArg₂ List.cons BatchLookup16.bound195 (congrArg₂ List.cons BatchLookup16.bound877 (congrArg₂ List.cons BatchLookup16.bound388 (congrArg₂ List.cons BatchLookup16.bound593 (congrArg₂ List.cons BatchLookup16.bound182 (congrArg₂ List.cons BatchLookup16.bound655 (congrArg₂ List.cons BatchLookup16.bound568 (congrArg₂ List.cons BatchLookup16.bound1050 (congrArg₂ List.cons BatchLookup16.bound379 (congrArg₂ List.cons BatchLookup16.bound549 (congrArg₂ List.cons BatchLookup16.bound672 (congrArg₂ List.cons BatchLookup16.bound960 (congrArg₂ List.cons BatchLookup16.bound140 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))))
  exact SourceMemo16_65.source.trans hb.symm
private theorem length65 : BatchLookup16.path65.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path65).length := by
  exact (congrArg List.length source65).symm
end SourceValues16



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

end PremiseCompact50

open Freiman
namespace BatchLookup16
set_option maxRecDepth 30000
private theorem size01 : lowerHistoryPremises01.size = 200 := by rfl
private theorem size02 : lowerHistoryPremises02.size = 200 := by rfl
private theorem size03 : lowerHistoryPremises03.size = 200 := by rfl
private theorem size04 : lowerHistoryPremises04.size = 200 := by rfl
private theorem size05 : lowerHistoryPremises05.size = 200 := by rfl
private theorem premise301 : lowerHistoryPremises[300]? = some ([3, 11, 21, 26, 43, 140, 182, 195, 260, 272, 371, 379, 388, 440, 549, 568, 593, 655, 672, 732, 774, 824, 833, 843, 856, 877, 960, 1050] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 300 = 200+100 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 100 (by decide)]
  rfl

private theorem premise303 : lowerHistoryPremises[302]? = some ([3, 11, 21, 26, 43, 140, 182, 260, 272, 371, 379, 388, 440, 549, 568, 593, 655, 672, 732, 774, 824, 833, 843, 856, 960, 1042, 1050] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 302 = 200+102 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 102 (by decide)]
  rfl

private theorem premise305 : lowerHistoryPremises[304]? = some ([3, 11, 21, 26, 43, 140, 195, 260, 272, 371, 379, 388, 440, 549, 593, 672, 732, 774, 824, 833, 843, 856, 877, 960, 1029] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 304 = 200+104 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 104 (by decide)]
  rfl

private theorem premise307 : lowerHistoryPremises[306]? = some ([3, 11, 21, 26, 43, 140, 260, 272, 371, 379, 388, 440, 549, 593, 672, 732, 774, 824, 833, 843, 856, 960, 1029, 1042] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 306 = 200+106 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 106 (by decide)]
  rfl

private theorem premise323 : lowerHistoryPremises[322]? = some ([3, 11, 21, 26, 43, 203, 260, 272, 371, 401, 405, 440, 539, 555, 643, 732, 774, 824, 833, 843, 856, 947, 1002, 1042] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 322 = 200+122 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 122 (by decide)]
  rfl

private theorem premise325 : lowerHistoryPremises[324]? = some ([3, 11, 21, 43, 183, 260, 272, 371, 395, 440, 620, 753, 774, 789, 824, 833, 843, 856, 1015, 1088, 1098, 1118] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 324 = 200+124 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 124 (by decide)]
  rfl

private theorem premise327 : lowerHistoryPremises[326]? = some ([3, 11, 21, 43, 197, 260, 272, 371, 398, 440, 666, 774, 786, 789, 824, 833, 843, 856, 1047, 1118] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 326 = 200+126 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 126 (by decide)]
  rfl

private theorem premise329 : lowerHistoryPremises[328]? = some ([3, 11, 21, 43, 236, 260, 272, 371, 440, 747, 774, 824, 829, 833, 843, 856, 1093] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 328 = 200+128 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 128 (by decide)]
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
private theorem coverage61 : (List.range path61.alternatives).all
    (coverageCheck path61 ([⟨.left,61,0,(-1),false,325,907⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage62 : (List.range path62.alternatives).all
    (coverageCheck path62 ([⟨.left,62,0,(-1),false,327,949⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage63 : (List.range path63.alternatives).all
    (coverageCheck path63 ([⟨.left,63,0,(-1),false,329,997⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage64 : (List.range path64.alternatives).all
    (coverageCheck path64 ([⟨.left,64,0,(-1),false,323,841⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage65 : (List.range path65.alternatives).all
    (coverageCheck path65 ([⟨.left,65,0,(-1),false,307,853⟩,⟨.left,65,1,(-1),false,303,853⟩,⟨.left,65,2,(-1),false,305,853⟩,⟨.left,65,3,(-1),false,301,853⟩] : List LowerHistoryRecord)) = true := by
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
private theorem path61_lookup : lowerHistoryPaths[60]? = some path61 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[10]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[60]? = some path61 :=
    (slice_get lowerHistoryPathsL.toList 10 (by decide)).symm.trans hs
  exact (first_lookup 60 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path62_lookup : lowerHistoryPaths[61]? = some path62 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[11]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[61]? = some path62 :=
    (slice_get lowerHistoryPathsL.toList 11 (by decide)).symm.trans hs
  exact (first_lookup 61 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path63_lookup : lowerHistoryPaths[62]? = some path63 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[12]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[62]? = some path63 :=
    (slice_get lowerHistoryPathsL.toList 12 (by decide)).symm.trans hs
  exact (first_lookup 62 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path64_lookup : lowerHistoryPaths[63]? = some path64 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[13]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[63]? = some path64 :=
    (slice_get lowerHistoryPathsL.toList 13 (by decide)).symm.trans hs
  exact (first_lookup 63 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path65_lookup : lowerHistoryPaths[64]? = some path65 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[14]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[64]? = some path65 :=
    (slice_get lowerHistoryPathsL.toList 14 (by decide)).symm.trans hs
  exact (first_lookup 64 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
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

private theorem witness997_projection :
    (lowerHistoryWitness 997).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 997).upperBound = lowerHistoryBound 1093 ∧
    (lowerHistoryWitness 997).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[196]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 1093, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 1093, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk5 196 (by decide))).trans hl

end WitnessLookup15

namespace WitnessLookup16
open Freiman

private theorem witness841_projection :
    (lowerHistoryWitness 841).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 841).upperBound = lowerHistoryBound 947 ∧
    (lowerHistoryWitness 841).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[40]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 947, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 947, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk5 40 (by decide))).trans hl

private theorem witness853_projection :
    (lowerHistoryWitness 853).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 853).upperBound = lowerHistoryBound 960 ∧
    (lowerHistoryWitness 853).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[52]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 960, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 960, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk5 52 (by decide))).trans hl

private theorem witness907_projection :
    (lowerHistoryWitness 907).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 907).upperBound = lowerHistoryBound 1015 ∧
    (lowerHistoryWitness 907).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[106]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 1015, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 1015, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk5 106 (by decide))).trans hl

private theorem witness949_projection :
    (lowerHistoryWitness 949).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 949).upperBound = lowerHistoryBound 1047 ∧
    (lowerHistoryWitness 949).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[148]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 1047, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 1047, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk5 148 (by decide))).trans hl

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
private def src61 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,272,774,11,789,1118,1098,1088,395,620,753,1015,183]]
private def recs61 : List LowerHistoryRecord := [⟨.left,61,0,(-1),false,325,907⟩]
private theorem check61 : recs61.all (recordCheck path61 src61 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path61_binding : lowerHistoryPathBinding path61 := by
  apply pathBinding_from_ids path61 src61 [] recs61 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source61 rfl records61 rfl
  · intro r hr _
    simp only [recs61, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise325)
  · intro r hr _
    simp only [recs61, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path61] using WitnessLookup16.witness907_projection
  · exact check61
  · exact BatchCoverage15.coverage_sound path61 recs61
      records61 SourceValues16.length61 BatchCoverageAll16.coverage61
private def src62 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,272,774,11,789,1118,398,666,786,1047,197]]
private def recs62 : List LowerHistoryRecord := [⟨.left,62,0,(-1),false,327,949⟩]
private theorem check62 : recs62.all (recordCheck path62 src62 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path62_binding : lowerHistoryPathBinding path62 := by
  apply pathBinding_from_ids path62 src62 [] recs62 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source62 rfl records62 rfl
  · intro r hr _
    simp only [recs62, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise327)
  · intro r hr _
    simp only [recs62, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path62] using WitnessLookup16.witness949_projection
  · exact check62
  · exact BatchCoverage15.coverage_sound path62 recs62
      records62 SourceValues16.length62 BatchCoverageAll16.coverage62
private def src63 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,272,774,11,236,747,829,1093]]
private def recs63 : List LowerHistoryRecord := [⟨.left,63,0,(-1),false,329,997⟩]
private theorem check63 : recs63.all (recordCheck path63 src63 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path63_binding : lowerHistoryPathBinding path63 := by
  apply pathBinding_from_ids path63 src63 [] recs63 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source63 rfl records63 rfl
  · intro r hr _
    simp only [recs63, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise329)
  · intro r hr _
    simp only [recs63, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path63] using WitnessLookup15.witness997_projection
  · exact check63
  · exact BatchCoverage15.coverage_sound path63 recs63
      records63 SourceValues16.length63 BatchCoverageAll16.coverage63
private def src64 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,1042,405,555,1002,401,539,643,947,203]]
private def recs64 : List LowerHistoryRecord := [⟨.left,64,0,(-1),false,323,841⟩]
private theorem check64 : recs64.all (recordCheck path64 src64 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path64_binding : lowerHistoryPathBinding path64 := by
  apply pathBinding_from_ids path64 src64 [] recs64 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source64 rfl records64 rfl
  · intro r hr _
    simp only [recs64, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise323)
  · intro r hr _
    simp only [recs64, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path64] using WitnessLookup16.witness841_projection
  · exact check64
  · exact BatchCoverage15.coverage_sound path64 recs64
      records64 SourceValues16.length64 BatchCoverageAll16.coverage64
private def src65 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,1042,388,593,1029,379,549,672,960,140],[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,1042,388,593,182,655,568,1050,379,549,672,960,140],[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,195,877,388,593,1029,379,549,672,960,140],[371,843,260,440,3,856,21,833,43,824,272,774,11,732,26,195,877,388,593,182,655,568,1050,379,549,672,960,140]]
private def recs65 : List LowerHistoryRecord := [⟨.left,65,0,(-1),false,307,853⟩,⟨.left,65,1,(-1),false,303,853⟩,⟨.left,65,2,(-1),false,305,853⟩,⟨.left,65,3,(-1),false,301,853⟩]
private theorem check65 : recs65.all (recordCheck path65 src65 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path65_binding : lowerHistoryPathBinding path65 := by
  apply pathBinding_from_ids path65 src65 [] recs65 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source65 rfl records65 rfl
  · intro r hr _
    simp only [recs65, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise307)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise303)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise305)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise301)
  · intro r hr _
    simp only [recs65, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [wids, path65] using WitnessLookup16.witness853_projection
    · simpa only [wids, path65] using WitnessLookup16.witness853_projection
    · simpa only [wids, path65] using WitnessLookup16.witness853_projection
    · simpa only [wids, path65] using WitnessLookup16.witness853_projection
  · exact check65
  · exact BatchCoverage15.coverage_sound path65 recs65
      records65 SourceValues16.length65 BatchCoverageAll16.coverage65
end BatchIdSolution50
theorem _root_.solution : lowerHistoryBindingBatch 60 65 := by
  intro i hlo hhi p hp
  interval_cases i
  · have he := Option.some.inj (PathLookup16.path61_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path61_binding
  · have he := Option.some.inj (PathLookup16.path62_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path62_binding
  · have he := Option.some.inj (PathLookup16.path63_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path63_binding
  · have he := Option.some.inj (PathLookup16.path64_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path64_binding
  · have he := Option.some.inj (PathLookup16.path65_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path65_binding
end M7Binding50Sep15
#print axioms solution
