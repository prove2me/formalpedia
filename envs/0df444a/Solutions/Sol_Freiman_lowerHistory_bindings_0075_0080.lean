-- Prove2me | solution 1 for Freiman.lowerHistory_bindings_0075_0080
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-15T10:00:38.814104+00:00
-- url     : https://prove2.me/submissions/2565d5c3-f248-4b5c-b8e5-d10cc88827e2

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
private theorem norm8 : lowerHistoryNormalization ([2,1,3],[3,1]) true false = ⟨true,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm9 : lowerHistoryNormalization ([2,1,3,1],[3,1]) true true = ⟨true,true,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm10 : lowerHistoryNormalization ([2,1,3],[3,1]) false false = ⟨false,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm14 : lowerHistoryNormalization ([2,1,3,1],[3,1]) false false = ⟨false,false,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm15 : lowerHistoryNormalization ([2,1,3,1,2],[3,1]) true true = ⟨true,true,⟨⟨(12451/1282630),0,0,(1281/1282630)⟩,⟨(167/470),0,0,(1/1410)⟩,⟨(1963/5458),0,0,(-1/5458)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm16 : lowerHistoryNormalization ([2,1,3,1,2,1],[3,1]) true true = ⟨true,true,⟨⟨(757/149554),0,0,(113/747770)⟩,⟨(167/470),0,0,(1/1410)⟩,⟨(5711/15910),0,0,(-1/15910)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm17 : lowerHistoryNormalization ([2,1,3,1,1],[3,1]) true false = ⟨true,false,⟨⟨(23577/1274354),0,0,(3059/1274354)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm18 : lowerHistoryNormalization ([2,1,3,1,1,1],[3,1]) true true = ⟨true,true,⟨⟨(16741/2214418),0,0,(1853/2214418)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(787/2186),0,0,(-1/6558)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm21 : lowerHistoryNormalization ([2,1,2],[3,1]) false false = ⟨false,false,⟨⟨(41/185),0,0,(32/1295)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm22 : lowerHistoryNormalization ([2,1,2,3],[3,1]) true true = ⟨true,true,⟨⟨(3211/109150),0,0,(49/109150)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm23 : lowerHistoryNormalization ([2,1,2,2],[3,1]) true true = ⟨true,true,⟨⟨(1671/46166),0,0,(1475/323162)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm38 : lowerHistoryNormalization ([2,1,3],[3]) true true = ⟨true,true,⟨⟨(5/17),0,0,(-4/85)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem norm39 : lowerHistoryNormalization ([2,1,2],[3]) true true = ⟨true,true,⟨⟨(43/370),0,0,(11/2590)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩ := by
  norm_num [lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey11 : lowerHistoryPull (lowerHistoryH2) ([2,1],[3]) false = ⟨true,true,⟨⟨(3418287291/5478244850),(-26216794/8217367275),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey12 : lowerHistoryPull (lowerHistoryH5) ([2,1],[3]) false = ⟨false,true,⟨⟨(33285470319/67820291500),(-327225429/33910145750),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey13 : lowerHistoryPull (lowerHistoryH6) ([2,1],[3]) false = ⟨false,true,⟨⟨(12374850333/44281430000),0,0,(547966053/44281430000)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey14 : lowerHistoryPull (lowerHistoryH7Mixed) ([2,1],[3]) false = ⟨false,true,⟨⟨(17288019/81914300),(23104949/409571500),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey15 : lowerHistoryPull (lowerHistoryH2) ([2,1,3],[3,1]) true = ⟨false,true,⟨⟨(329014964650/1370729503247),(2276619750/1370729503247),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(12510/34801),(1/34801),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey16 : lowerHistoryPull (lowerHistoryH7) ([2,1,3,1],[3,1]) true = ⟨false,false,⟨⟨(1595970350/4021318543),(-455592800/4021318543),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey17 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,3,1],[3,1]) true = ⟨false,true,⟨⟨(1322907/23585446),(2312189/70756338),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey18 : lowerHistoryPull (lowerHistoryHN) ([2,1,3,1],[3,1]) true = ⟨true,false,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey29 : lowerHistoryPull (lowerHistoryH7) ([2,1,3,1],[3,1]) false = ⟨true,false,⟨⟨(3023864/142697685),(8765033/1426976850),0,0⟩,⟨(713/1991),(1/5973),0,0⟩,⟨(112/311),(-1/933),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey30 : lowerHistoryPull (lowerHistoryH9) ([2,1,3,1],[3,1]) false = ⟨false,false,⟨⟨(-3927621/1876381),(2328691/1876381),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey31 : lowerHistoryPull (lowerHistoryH2) ([2,1,3,1,2],[3,1]) true = ⟨false,true,⟨⟨(4537435526450/260705437441007),(29126250350/260705437441007),0,0⟩,⟨(62780/175069),(-1/175069),0,0⟩,⟨(170829/476302),(1/476302),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey32 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,3,1,2],[3,1]) true = ⟨false,false,⟨⟨(6371851756000/289452087377667),(142586805500/289452087377667),0,0⟩,⟨(170829/476302),(1/476302),0,0⟩,⟨(8732/24337),(-1/24337),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey33 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,1,3,1,2],[3,1]) true = ⟨false,false,⟨⟨(234826021/32720177708),(676296307/98160533124),0,0⟩,⟨(3679/10259),(1/30777),0,0⟩,⟨(286090/797353),(-1/797353),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey34 : lowerHistoryPull (lowerHistoryH23) ([2,1,3,1,2],[3,1]) true = ⟨false,true,⟨⟨(874485720750/35239157983159),(-35376316250/35239157983159),0,0⟩,⟨(170829/476302),(1/476302),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey35 : lowerHistoryPull (lowerHistoryH7) ([2,1,3,1,2,1],[3,1]) true = ⟨false,false,⟨⟨(130654600/4561532107),(-37210050/4561532107),0,0⟩,⟨(19569/54574),(1/54574),0,0⟩,⟨(29714/82849),(-1/82849),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey36 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,3,1,2,1],[3,1]) true = ⟨false,true,⟨⟨(1411141/347800102),(2466337/1043400306),0,0⟩,⟨(19569/54574),(1/54574),0,0⟩,⟨(29714/82849),(-1/82849),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey37 : lowerHistoryPull (lowerHistoryHN) ([2,1,3,1,2,1],[3,1]) true = ⟨true,false,⟨⟨(757/149554),0,0,(113/747770)⟩,⟨(167/470),0,0,(1/1410)⟩,⟨(5711/15910),0,0,(-1/15910)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey38 : lowerHistoryPull (lowerHistoryH2) ([2,1,3,1,1],[3,1]) true = ⟨false,true,⟨⟨(20528290950/592342509109),(12388023950/65750018511099),0,0⟩,⟨(10689/29759),(-1/89277),0,0⟩,⟨(84635/235558),(1/235558),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey39 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH5) ([2,1,3,1,1],[3,1]) true = ⟨false,false,⟨⟨(336374075000/7268192617191),(33481634500/65413733554719),0,0⟩,⟨(84635/235558),(1/235558),0,0⟩,⟨(1333/3707),(-1/11121),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey40 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH21) ([2,1,3,1,1],[3,1]) true = ⟨false,false,⟨⟨(347098019/22688659108),(328084023/22688659108),0,0⟩,⟨(5604/15601),(1/15601),0,0⟩,⟨(130741/363577),(-1/363577),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey41 : lowerHistoryPull (lowerHistoryH23) ([2,1,3,1,1],[3,1]) true = ⟨false,true,⟨⟨(427469976750/8363874636247),(-26565444250/8363874636247),0,0⟩,⟨(84635/235558),(1/235558),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey42 : lowerHistoryPull (lowerHistoryH7) ([2,1,3,1,1,1],[3,1]) true = ⟨false,false,⟨⟨(3719933100/65823028469),(-3164441150/197469085407),0,0⟩,⟨(10127/28198),(1/28198),0,0⟩,⟨(4919/13691),(-1/41073),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey43 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH9) ([2,1,3,1,1,1],[3,1]) true = ⟨false,true,⟨⟨(9311221/1158176454),(5424319/1158176454),0,0⟩,⟨(10127/28198),(1/28198),0,0⟩,⟨(4919/13691),(-1/41073),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩ := by
  norm_num [lowerHistoryPull, lowerHistoryComplement, h2, h5, h6, h7, h7m, h9, h21, h23, hn, bh2, bh5, bh6, bh7, bh7m, bh9, bh21, bh23, bhn, lowerHistoryNormalization, lowerHistoryWH, lowerHistoryCF, lowerHistoryMatrix, lowerHistoryThreshold, lowerHistorySort, lowerHistoryLex, lowerHistoryAbs, lowerHistoryDiv, RootInv18.quadratic_three, RootInv18.quadratic_twenty_one, lowerHistorySign, lowerHistoryQuadSign, lowerHistoryRatSign, lowerHistoryNeg, lowerHistoryAlpha, lowerHistoryBeta, lowerHistoryTau, lowerHistoryRat, certFieldScale, certFieldMul, certFieldAdd, certFieldSub]
private theorem pullKey44 : lowerHistoryPull (lowerHistoryHN) ([2,1,3,1,1,1],[3,1]) true = ⟨true,false,⟨⟨(16741/2214418),0,0,(1853/2214418)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(787/2186),0,0,(-1/6558)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩ := by
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
private theorem pull11 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = ⟨false,false,⟨⟨(3418287291/5478244850),(-26216794/8217367275),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey11]
  rfl
private theorem pull31 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH7) ([2,1,3,1],[3,1]) false = ⟨false,true,⟨⟨(3023864/142697685),(8765033/1426976850),0,0⟩,⟨(713/1991),(1/5973),0,0⟩,⟨(112/311),(-1/933),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey29]
  rfl
private theorem pull35 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,3,1,2],[3,1]) true = ⟨true,false,⟨⟨(4537435526450/260705437441007),(29126250350/260705437441007),0,0⟩,⟨(62780/175069),(-1/175069),0,0⟩,⟨(170829/476302),(1/476302),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey31]
  rfl
private theorem pull43 : lowerHistoryPull (lowerHistoryComplement lowerHistoryH2) ([2,1,3,1,1],[3,1]) true = ⟨true,false,⟨⟨(20528290950/592342509109),(12388023950/65750018511099),0,0⟩,⟨(10689/29759),(-1/89277),0,0⟩,⟨(84635/235558),(1/235558),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩ := by
  rw [RootPull18.complement, pullKey38]
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
private theorem branchesG5 :
    (lowerHistoryNecessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,3],[3,1]) = some [⟨false,false,⟨⟨(1586290/10727197),(3840344/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2],[3,1,3]),(true,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,1,2],[3]) = some [⟨false,false,⟨⟨(2953/30251),(8625/30251),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,2],[3,1]) = some [⟨true,false,⟨⟨(-5111577/15657181),(3840568/15657181),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,2],[3,1]) = some [⟨false,false,⟨⟨(7617/30251),(63275/90753),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1],[3,1,3]),(true,true)⟩,true,false,some (false,([1],[]),true)⟩ ([2,1,1],[3]) = some [⟨false,false,⟨⟨(13766/50713),(29019/50713),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,1],[3,1]) = some [⟨true,false,⟨⟨(-2396241/3388429),(1794784/3388429),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,1,1],[3,1]) = some [⟨true,false,⟨⟨(-271911/1001627),(203584/1001627),0,0⟩,⟨(446/1177),(1/1177),0,0⟩,⟨(651/1702),(-1/1702),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩])
    ∧ (lowerHistoryNecessary ⟨⟨([1,2,1,1,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,1,1,3],[3,1]) = some [⟨false,false,⟨⟨(14928072/698102327),(107382092/2094306981),0,0⟩,⟨(231/611),(1/1833),0,0⟩,⟨(33275/87889),(-1/87889),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩]) := by
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
end BindingSourceSupport16

open Freiman
open RootOps19
set_option linter.all false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace BindingOps16_76
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b20 : CertBound) (b21 : CertBound) (b42 : CertBound) (b43 : CertBound) (b130 : CertBound) (b166 : CertBound) (b175 : CertBound) (b260 : CertBound) (b371 : CertBound) (b373 : CertBound) (b381 : CertBound) (b421 : CertBound) (b440 : CertBound) (b445 : CertBound) (b524 : CertBound) (b532 : CertBound) (b554 : CertBound) (b612 : CertBound) (b642 : CertBound) (b692 : CertBound) (b795 : CertBound) (b806 : CertBound) (b824 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b946 : CertBound) (b1003 : CertBound) (b1013 : CertBound) (b1024 : CertBound) (b1124 : CertBound) (b1138 : CertBound) (b1150 : CertBound)
private def path : LowerHistoryPath := ⟨.left,76,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,1,3],[3]) = some [b692])
    (hb3 : ops.necessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,3],[3,1]) = some [b20])
    (hb4 : ops.necessary ⟨⟨([1,2,1,3,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,3,1],[3,1]) = some [b42])
    (hb5 : ops.necessary ⟨⟨([1,2,1,3,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,3,1,2],[3,1]) = some [b554])
    (hb6 : ops.necessary ⟨⟨([1,2,1,3,1,2,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,3,1,2,1],[3,1]) = some [b524])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryH5) ([2,1],[3]) false = b1150)
    (hn4 : ops.pull (lowerHistoryH6) ([2,1],[3]) false = b1138)
    (hn5 : ops.pull (lowerHistoryH7Mixed) ([2,1],[3]) false = b1124)
    (hn6 : ops.normalization ([2,1,3],[3]) true true = b421)
    (hn7 : ops.normalization ([2,1,3],[3,1]) false false = b806)
    (hn8 : ops.normalization ([2,1,3,1],[3,1]) false false = b795)
    (hn9 : ops.pull (lowerHistoryComplement lowerHistoryH7) ([2,1,3,1],[3,1]) false = b1013)
    (hn10 : ops.pull (lowerHistoryH7) ([2,1,3,1],[3,1]) false = b175)
    (hn11 : ops.pull (lowerHistoryH9) ([2,1,3,1],[3,1]) false = b445)
    (hn12 : ops.normalization ([2,1,3,1,2],[3,1]) true true = b381)
    (hn13 : ops.pull (lowerHistoryH2) ([2,1,3,1,2],[3,1]) true = b1003)
    (hn14 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,3,1,2],[3,1]) true = b166)
    (hn15 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,3,1,2],[3,1]) true = b612)
    (hn16 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1,3,1,2],[3,1]) true = b532)
    (hn17 : ops.pull (lowerHistoryH23) ([2,1,3,1,2],[3,1]) true = b1024)
    (hn18 : ops.normalization ([2,1,3,1,2,1],[3,1]) true true = b373)
    (hn19 : ops.pull (lowerHistoryH7) ([2,1,3,1,2,1],[3,1]) true = b642)
    (hn20 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,3,1,2,1],[3,1]) true = b946)
    (hn21 : ops.pull (lowerHistoryHN) ([2,1,3,1,2,1],[3,1]) true = b130)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b1003,b373,b524,b642,b946,b130].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130]
] : List (List CertBound))[1])
    (herase2 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b1003,b373,b524,b642,b946,b130].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130]
] : List (List CertBound))[2])
    (herase3 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130]
] : List (List CertBound))[3])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b1013,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b1003,b373,b524,b642,b946,b130],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b175,b445,b381,b554,b166,b612,b532,b1024,b373,b524,b642,b946,b130]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7Mixed]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice4 : lowerHistorySourceChoices ⟨⟨([1,2,1,3,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH7],[lowerHistoryH7,lowerHistoryH9]] := by rfl
  have hdone4 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced4 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice5 : lowerHistorySourceChoices ⟨⟨([1,2,1,3,1,2],[3,1,3,1]),(true,false)⟩,true,true,some (false,([2],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone5 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced5 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hn19, hn20, hn21, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, hchoice4, hdone4, hforced4, hchoice5, hdone5, hforced5, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1, herase2, herase3]
  rfl
end BindingOps16_76
namespace BindingOps16_77
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b20 : CertBound) (b21 : CertBound) (b42 : CertBound) (b43 : CertBound) (b138 : CertBound) (b169 : CertBound) (b194 : CertBound) (b260 : CertBound) (b371 : CertBound) (b377 : CertBound) (b421 : CertBound) (b440 : CertBound) (b563 : CertBound) (b584 : CertBound) (b637 : CertBound) (b668 : CertBound) (b690 : CertBound) (b692 : CertBound) (b795 : CertBound) (b806 : CertBound) (b824 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b968 : CertBound) (b1041 : CertBound) (b1066 : CertBound) (b1124 : CertBound) (b1138 : CertBound) (b1150 : CertBound)
private def path : LowerHistoryPath := ⟨.left,77,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,1,3],[3]) = some [b692])
    (hb3 : ops.necessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,3],[3,1]) = some [b20])
    (hb4 : ops.necessary ⟨⟨([1,2,1,3,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([2,1,3,1],[3,1]) = some [b42])
    (hb5 : ops.necessary ⟨⟨([1,2,1,3,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([2,1,3,1,1],[3,1]) = some [b637])
    (hb6 : ops.necessary ⟨⟨([1,2,1,3,1,1,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,3,1,1,1],[3,1]) = some [b563])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryH5) ([2,1],[3]) false = b1150)
    (hn4 : ops.pull (lowerHistoryH6) ([2,1],[3]) false = b1138)
    (hn5 : ops.pull (lowerHistoryH7Mixed) ([2,1],[3]) false = b1124)
    (hn6 : ops.normalization ([2,1,3],[3]) true true = b421)
    (hn7 : ops.normalization ([2,1,3],[3,1]) false false = b806)
    (hn8 : ops.normalization ([2,1,3,1],[3,1]) false false = b795)
    (hn9 : ops.normalization ([2,1,3,1,1],[3,1]) true false = b169)
    (hn10 : ops.pull (lowerHistoryH2) ([2,1,3,1,1],[3,1]) true = b1041)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,3,1,1],[3,1]) true = b194)
    (hn12 : ops.pull (lowerHistoryComplement lowerHistoryH5) ([2,1,3,1,1],[3,1]) true = b668)
    (hn13 : ops.pull (lowerHistoryComplement lowerHistoryH21) ([2,1,3,1,1],[3,1]) true = b584)
    (hn14 : ops.pull (lowerHistoryH23) ([2,1,3,1,1],[3,1]) true = b1066)
    (hn15 : ops.normalization ([2,1,3,1,1,1],[3,1]) true true = b377)
    (hn16 : ops.pull (lowerHistoryH7) ([2,1,3,1,1,1],[3,1]) true = b690)
    (hn17 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,3,1,1,1],[3,1]) true = b968)
    (hn18 : ops.pull (lowerHistoryHN) ([2,1,3,1,1,1],[3,1]) true = b138)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b169,b637,b1041,b377,b563,b690,b968,b138].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b169,b637,b1041,b377,b563,b690,b968,b138],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b169,b637,b194,b668,b584,b1066,b377,b563,b690,b968,b138]
] : List (List CertBound))[0])
    (herase1 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b169,b637,b194,b668,b584,b1066,b377,b563,b690,b968,b138].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b169,b637,b1041,b377,b563,b690,b968,b138],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b169,b637,b194,b668,b584,b1066,b377,b563,b690,b968,b138]
] : List (List CertBound))[1])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b169,b637,b1041,b377,b563,b690,b968,b138],
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b806,b20,b795,b42,b169,b637,b194,b668,b584,b1066,b377,b563,b690,b968,b138]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7Mixed]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice4 : lowerHistorySourceChoices ⟨⟨([1,2,1,3,1],[3,1,3,1]),(false,false)⟩,false,true,some (false,([1],[]),false)⟩ ([1],[]) = [[]] := by rfl
  have hdone4 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced4 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice5 : lowerHistorySourceChoices ⟨⟨([1,2,1,3,1,1],[3,1,3,1]),(true,false)⟩,true,true,some (false,([1],[]),true)⟩ ([],[1]) = [[lowerHistoryH2],[lowerHistoryComplement lowerHistoryH2,lowerHistoryComplement lowerHistoryH5,lowerHistoryComplement lowerHistoryH21,lowerHistoryH23]] := by rfl
  have hdone5 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced5 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hn14, hn15, hn16, hn17, hn18, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, hchoice4, hdone4, hforced4, hchoice5, hdone5, hforced5, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0, herase1]
  rfl
end BindingOps16_77
namespace BindingOps16_78
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b21 : CertBound) (b43 : CertBound) (b260 : CertBound) (b262 : CertBound) (b263 : CertBound) (b371 : CertBound) (b421 : CertBound) (b423 : CertBound) (b440 : CertBound) (b692 : CertBound) (b736 : CertBound) (b752 : CertBound) (b809 : CertBound) (b824 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1071 : CertBound) (b1124 : CertBound) (b1132 : CertBound) (b1138 : CertBound) (b1150 : CertBound)
private def path : LowerHistoryPath := ⟨.left,78,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),false),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([2,1,3],[3]) = some [b692])
    (hb3 : ops.necessary ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([2,1,3],[3,1]) = some [b752])
    (hb4 : ops.necessary ⟨⟨([1,2,1,3,1],[3,1,3,1]),(false,false)⟩,true,true,some (true,([],[1]),false)⟩ ([2,1,3,1],[3,1]) = some [b736])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryH5) ([2,1],[3]) false = b1150)
    (hn4 : ops.pull (lowerHistoryH6) ([2,1],[3]) false = b1138)
    (hn5 : ops.pull (lowerHistoryH7Mixed) ([2,1],[3]) false = b1124)
    (hn6 : ops.normalization ([2,1,3],[3]) true true = b421)
    (hn7 : ops.normalization ([2,1,3],[3,1]) true false = b263)
    (hn8 : ops.pull (lowerHistoryH2) ([2,1,3],[3,1]) true = b1132)
    (hn9 : ops.normalization ([2,1,3,1],[3,1]) true true = b423)
    (hn10 : ops.pull (lowerHistoryH7) ([2,1,3,1],[3,1]) true = b809)
    (hn11 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,3,1],[3,1]) true = b1071)
    (hn12 : ops.pull (lowerHistoryHN) ([2,1,3,1],[3,1]) true = b262)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b263,b752,b1132,b423,b736,b809,b1071,b262].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b263,b752,b1132,b423,b736,b809,b1071,b262]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b1138,b1124,b421,b692,b263,b752,b1132,b423,b736,b809,b1071,b262]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7Mixed]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,3],[3,1,3]),(true,true)⟩,true,false,some (false,([3],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,3],[3,1,3,1]),(true,false)⟩,true,true,some (true,([1],[]),false)⟩ ([],[1]) = [[lowerHistoryH2]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([],[1]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps16_78
namespace BindingOps16_79
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b11 : CertBound) (b21 : CertBound) (b43 : CertBound) (b183 : CertBound) (b260 : CertBound) (b371 : CertBound) (b395 : CertBound) (b415 : CertBound) (b440 : CertBound) (b620 : CertBound) (b726 : CertBound) (b753 : CertBound) (b774 : CertBound) (b789 : CertBound) (b824 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1015 : CertBound) (b1088 : CertBound) (b1098 : CertBound) (b1118 : CertBound) (b1150 : CertBound)
private def path : LowerHistoryPath := ⟨.left,79,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([3],[]),true)],([1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3]),(true,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,1,2],[3]) = some [b726])
    (hb3 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,2],[3,1]) = some [b11])
    (hb4 : ops.necessary ⟨⟨([1,2,1,2,3],[3,1,3,1]),(false,false)⟩,true,true,some (false,([3],[]),true)⟩ ([2,1,2,3],[3,1]) = some [b620])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryH5) ([2,1],[3]) false = b1150)
    (hn4 : ops.normalization ([2,1,2],[3]) true true = b415)
    (hn5 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (hn6 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) false = b789)
    (hn7 : ops.pull (lowerHistoryH5) ([2,1,2],[3,1]) false = b1118)
    (hn8 : ops.pull (lowerHistoryH6) ([2,1,2],[3,1]) false = b1098)
    (hn9 : ops.pull (lowerHistoryH7Mixed) ([2,1,2],[3,1]) false = b1088)
    (hn10 : ops.normalization ([2,1,2,3],[3,1]) true true = b395)
    (hn11 : ops.pull (lowerHistoryH7) ([2,1,2,3],[3,1]) true = b753)
    (hn12 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,3],[3,1]) true = b1015)
    (hn13 : ops.pull (lowerHistoryHN) ([2,1,2,3],[3,1]) true = b183)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b415,b726,b774,b11,b789,b1118,b1098,b1088,b395,b620,b753,b1015,b183].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b415,b726,b774,b11,b789,b1118,b1098,b1088,b395,b620,b753,b1015,b183]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b415,b726,b774,b11,b789,b1118,b1098,b1088,b395,b620,b753,b1015,b183]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3]),(true,true)⟩,true,false,some (false,([2],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([3],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5,lowerHistoryH6,lowerHistoryH7Mixed]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([3],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hn12, hn13, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps16_79
namespace BindingOps16_80
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.all false
variable (ops : SourceOps) (b3 : CertBound) (b11 : CertBound) (b21 : CertBound) (b43 : CertBound) (b197 : CertBound) (b260 : CertBound) (b371 : CertBound) (b398 : CertBound) (b415 : CertBound) (b440 : CertBound) (b666 : CertBound) (b726 : CertBound) (b774 : CertBound) (b786 : CertBound) (b789 : CertBound) (b824 : CertBound) (b833 : CertBound) (b843 : CertBound) (b856 : CertBound) (b1047 : CertBound) (b1118 : CertBound) (b1150 : CertBound)
private def path : LowerHistoryPath := ⟨.left,80,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([2],[]),true)],([1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private theorem source_structural
    (hrel : ops.relaxed ⟨([1],[3,1]),(false,false)⟩ = some [b3])
    (hbase : [lowerHistoryZero,lowerHistoryHN,lowerHistoryH7,lowerHistoryComplement lowerHistoryH9] =
      [b371,b843,b260,b440])
    (hb0 : ops.necessary ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([2],[3]) = some [b21])
    (hb1 : ops.necessary ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2,1],[3]) = some [b43])
    (hb2 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3]),(true,true)⟩,true,false,some (false,([2],[]),true)⟩ ([2,1,2],[3]) = some [b726])
    (hb3 : ops.necessary ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2,1,2],[3,1]) = some [b11])
    (hb4 : ops.necessary ⟨⟨([1,2,1,2,2],[3,1,3,1]),(false,false)⟩,true,true,some (false,([2],[]),true)⟩ ([2,1,2,2],[3,1]) = some [b666])
    (hn0 : ops.normalization ([2],[3]) false false = b856)
    (hn1 : ops.normalization ([2,1],[3]) false false = b833)
    (hn2 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1],[3]) false = b824)
    (hn3 : ops.pull (lowerHistoryH5) ([2,1],[3]) false = b1150)
    (hn4 : ops.normalization ([2,1,2],[3]) true true = b415)
    (hn5 : ops.normalization ([2,1,2],[3,1]) false false = b774)
    (hn6 : ops.pull (lowerHistoryComplement lowerHistoryH2) ([2,1,2],[3,1]) false = b789)
    (hn7 : ops.pull (lowerHistoryH5) ([2,1,2],[3,1]) false = b1118)
    (hn8 : ops.normalization ([2,1,2,2],[3,1]) true true = b398)
    (hn9 : ops.pull (lowerHistoryH7) ([2,1,2,2],[3,1]) true = b786)
    (hn10 : ops.pull (lowerHistoryComplement lowerHistoryH9) ([2,1,2,2],[3,1]) true = b1047)
    (hn11 : ops.pull (lowerHistoryHN) ([2,1,2,2],[3,1]) true = b197)
    (herase0 : [b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b415,b726,b774,b11,b789,b1118,b398,b666,b786,b1047,b197].eraseDups = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b415,b726,b774,b11,b789,b1118,b398,b666,b786,b1047,b197]
] : List (List CertBound))[0])
    : eval ops path = ([
[b371,b843,b260,b440,b3,b856,b21,b833,b43,b824,b1150,b415,b726,b774,b11,b789,b1118,b398,b666,b786,b1047,b197]
] : List (List CertBound)) := by
  have hdone : decide (([3] : List ℕ+) ≠ []) = true := rfl
  have hchoice0 : lowerHistorySourceChoices ⟨⟨([1,2],[3,1,3]),(true,true)⟩,false,false,none⟩ ([1],[]) = [[]] := by rfl
  have hdone0 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced0 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice1 : lowerHistorySourceChoices ⟨⟨([1,2,1],[3,1,3]),(false,true)⟩,false,false,some (false,([1],[]),false)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5]] := by rfl
  have hdone1 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced1 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hchoice2 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3]),(true,true)⟩,true,false,some (false,([2],[]),true)⟩ ([1],[]) = [[]] := by rfl
  have hdone2 : decide (([1] : List ℕ+) ≠ []) = true := rfl
  have hforced2 : decide (([1],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = false := by rfl
  have hchoice3 : lowerHistorySourceChoices ⟨⟨([1,2,1,2],[3,1,3,1]),(true,false)⟩,false,true,some (true,([1],[]),true)⟩ ([2],[]) = [[lowerHistoryComplement lowerHistoryH2,lowerHistoryH5]] := by rfl
  have hdone3 : decide (([] : List ℕ+) ≠ []) = false := rfl
  have hforced3 : decide (([2],[]) ∈ [(([2],[]) : LowerLabel),([3],[]),([],[1])]) = true := by rfl
  have hidpure (x : List (List CertBound)) : (pure x : Id _).run = x := rfl
  unfold eval
  simp only [path, hrel, hbase, hb0, hb1, hb2, hb3, hb4, hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hn8, hn9, hn10, hn11, hdone, hchoice0, hdone0, hforced0, hchoice1, hdone1, hforced1, hchoice2, hdone2, hforced2, hchoice3, hdone3, hforced3, reduceCtorEq, show (2 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 1 from by decide, show (3 : ℕ) ≠ 2 from by decide, show (4 : ℕ) ≠ 1 from by decide, show (4 : ℕ) ≠ 2 from by decide, Bool.decide_and, Bool.false_and, Bool.true_and, Bool.and_false, Bool.and_true, if_false, if_true, decide_false, decide_true, Bool.false_eq_true, Bool.true_eq_false, Bool.not_false, Bool.not_true, Bool.xor_false, Bool.xor_true, Bool.false_or, Bool.true_or, or_false, true_or, or_true, eq_self_iff_true, List.reverseAux_cons, List.reverseAux_nil, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.length, List.forIn_cons, List.forIn_nil, pure_bind, lowerHistoryFinalCuts, lowerHistoryInitialState, lowerHistoryRawStep, lowerHistoryAdvance, lowerHistoryOrient, List.map, List.flatMap, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, hidpure]
  rw [herase0]
  rfl
end BindingOps16_80

open Freiman

private def sourceBound3 : CertBound := ⟨true,false,⟨⟨(-363/299),(257/299),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(1/2),(1/6),0,0⟩⟩⟩

private def sourceBound11 : CertBound := ⟨true,false,⟨⟨(-5111577/15657181),(3840568/15657181),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def sourceBound20 : CertBound := ⟨true,false,⟨⟨(-8845164/47149609),(6653521/47149609),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(667/1846),(-1/1846),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def sourceBound21 : CertBound := ⟨true,false,⟨⟨(-2609/14053),(33053/84318),0,0⟩,⟨(35/94),(1/94),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def sourceBound42 : CertBound := ⟨true,false,⟨⟨(-21593634/271232629),(16126691/271232629),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(16/59),(1/177),0,0⟩⟩⟩

private def sourceBound43 : CertBound := ⟨true,false,⟨⟨(-27041/364702),(168601/1094106),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩⟩⟩

private def sourceBound130 : CertBound := ⟨true,false,⟨⟨(757/149554),0,0,(113/747770)⟩,⟨(167/470),0,0,(1/1410)⟩,⟨(5711/15910),0,0,(-1/15910)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound138 : CertBound := ⟨true,false,⟨⟨(16741/2214418),0,0,(1853/2214418)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(787/2186),0,0,(-1/6558)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound166 : CertBound := ⟨true,false,⟨⟨(4537435526450/260705437441007),(29126250350/260705437441007),0,0⟩,⟨(62780/175069),(-1/175069),0,0⟩,⟨(170829/476302),(1/476302),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound169 : CertBound := ⟨true,false,⟨⟨(23577/1274354),0,0,(3059/1274354)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound175 : CertBound := ⟨true,false,⟨⟨(3023864/142697685),(8765033/1426976850),0,0⟩,⟨(713/1991),(1/5973),0,0⟩,⟨(112/311),(-1/933),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound183 : CertBound := ⟨true,false,⟨⟨(3211/109150),0,0,(49/109150)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound194 : CertBound := ⟨true,false,⟨⟨(20528290950/592342509109),(12388023950/65750018511099),0,0⟩,⟨(10689/29759),(-1/89277),0,0⟩,⟨(84635/235558),(1/235558),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound197 : CertBound := ⟨true,false,⟨⟨(1671/46166),0,0,(1475/323162)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound260 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,(-1),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private def sourceBound262 : CertBound := ⟨true,false,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound263 : CertBound := ⟨true,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound371 : CertBound := ⟨true,true,⟨⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩,⟨0,0,0,0⟩⟩⟩

private def sourceBound373 : CertBound := ⟨true,true,⟨⟨(757/149554),0,0,(113/747770)⟩,⟨(167/470),0,0,(1/1410)⟩,⟨(5711/15910),0,0,(-1/15910)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound377 : CertBound := ⟨true,true,⟨⟨(16741/2214418),0,0,(1853/2214418)⟩,⟨(723/2026),0,0,(1/2026)⟩,⟨(787/2186),0,0,(-1/6558)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound381 : CertBound := ⟨true,true,⟨⟨(12451/1282630),0,0,(1281/1282630)⟩,⟨(167/470),0,0,(1/1410)⟩,⟨(1963/5458),0,0,(-1/5458)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound395 : CertBound := ⟨true,true,⟨⟨(3211/109150),0,0,(49/109150)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound398 : CertBound := ⟨true,true,⟨⟨(1671/46166),0,0,(1475/323162)⟩,⟨(411/1126),0,0,(1/1126)⟩,⟨(31/82),0,0,(-1/574)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound415 : CertBound := ⟨true,true,⟨⟨(43/370),0,0,(11/2590)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def sourceBound421 : CertBound := ⟨true,true,⟨⟨(5/17),0,0,(-4/85)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def sourceBound423 : CertBound := ⟨true,true,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound440 : CertBound := ⟨true,true,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩

private def sourceBound445 : CertBound := ⟨false,false,⟨⟨(-3927621/1876381),(2328691/1876381),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound524 : CertBound := ⟨false,false,⟨⟨(5054340/840078733),(27711379/2520236199),0,0⟩,⟨(3679/10259),(1/30777),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound532 : CertBound := ⟨false,false,⟨⟨(234826021/32720177708),(676296307/98160533124),0,0⟩,⟨(3679/10259),(1/30777),0,0⟩,⟨(286090/797353),(-1/797353),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound554 : CertBound := ⟨false,false,⟨⟨(3334901/319441187),(9556540/319441187),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound563 : CertBound := ⟨false,false,⟨⟨(6926918/613103699),(13570693/613103699),0,0⟩,⟨(5604/15601),(1/15601),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound584 : CertBound := ⟨false,false,⟨⟨(347098019/22688659108),(328084023/22688659108),0,0⟩,⟨(5604/15601),(1/15601),0,0⟩,⟨(130741/363577),(-1/363577),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound612 : CertBound := ⟨false,false,⟨⟨(6371851756000/289452087377667),(142586805500/289452087377667),0,0⟩,⟨(170829/476302),(1/476302),0,0⟩,⟨(8732/24337),(-1/24337),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private def sourceBound620 : CertBound := ⟨false,false,⟨⟨(42724568/1681253509),(96584076/1681253509),0,0⟩,⟨(28970/78049),(1/78049),0,0⟩,⟨(616/1657),(-1/1657),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound637 : CertBound := ⟨false,false,⟨⟨(2408143/87283079),(5086662/87283079),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound642 : CertBound := ⟨false,false,⟨⟨(130654600/4561532107),(-37210050/4561532107),0,0⟩,⟨(19569/54574),(1/54574),0,0⟩,⟨(29714/82849),(-1/82849),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound666 : CertBound := ⟨false,false,⟨⟨(972280/21096959),(2470191/21096959),0,0⟩,⟨(1161/3142),(1/3142),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound668 : CertBound := ⟨false,false,⟨⟨(336374075000/7268192617191),(33481634500/65413733554719),0,0⟩,⟨(84635/235558),(1/235558),0,0⟩,⟨(1333/3707),(-1/11121),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1251/4667),(-1/14001),0,0⟩⟩⟩

private def sourceBound690 : CertBound := ⟨false,false,⟨⟨(3719933100/65823028469),(-3164441150/197469085407),0,0⟩,⟨(10127/28198),(1/28198),0,0⟩,⟨(4919/13691),(-1/41073),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound692 : CertBound := ⟨false,false,⟨⟨(619410/10727197),(1569896/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def sourceBound726 : CertBound := ⟨false,false,⟨⟨(2953/30251),(8625/30251),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(66/179),(-1/537),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def sourceBound736 : CertBound := ⟨false,false,⟨⟨(21401836/181871027),(16030791/181871027),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(797/2221),(1/2221),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound752 : CertBound := ⟨false,false,⟨⟨(1586290/10727197),(3840344/10727197),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound753 : CertBound := ⟨false,false,⟨⟨(2709504850/17611227007),(-2273395150/52833681021),0,0⟩,⟨(4178/11269),(1/11269),0,0⟩,⟨(1701/4583),(-1/13749),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound774 : CertBound := ⟨false,false,⟨⟨(41/185),0,0,(32/1295)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(29/74),0,0,(-1/222)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound786 : CertBound := ⟨false,false,⟨⟨(114542650/408037531),(-96533350/1224112593),0,0⟩,⟨(735/1991),(1/5973),0,0⟩,⟨(2890/7813),(-1/7813),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound789 : CertBound := ⟨false,false,⟨⟨(154748703689/531731481700),(100050183/265865740850),0,0⟩,⟨(483/1318),(1/1318),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩

private def sourceBound795 : CertBound := ⟨false,false,⟨⟨(1011/3145),0,0,(-166/3145)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(457/1258),0,0,(-1/1258)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound806 : CertBound := ⟨false,false,⟨⟨(13/34),0,0,(-7/170)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound809 : CertBound := ⟨false,false,⟨⟨(1595970350/4021318543),(-455592800/4021318543),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(126/481),(1/481),0,0⟩,⟨(21/73),(-1/73),0,0⟩⟩⟩

private def sourceBound824 : CertBound := ⟨false,false,⟨⟨(3418287291/5478244850),(-26216794/8217367275),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(32/83),(-1/249),0,0⟩,⟨(271/1006),(-1/1006),0,0⟩,⟨(767/2749),(1/2749),0,0⟩⟩⟩

private def sourceBound833 : CertBound := ⟨false,false,⟨⟨(7/10),0,0,(1/70)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(1/2),0,0,(-1/42)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def sourceBound843 : CertBound := ⟨false,false,⟨⟨1,0,0,0⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(-3/2),0,0,(1/2)⟩,⟨(-1/2),0,0,(1/6)⟩⟩⟩

private def sourceBound856 : CertBound := ⟨false,false,⟨⟨(3/2),0,0,(1/10)⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(9/10),0,0,(-1/10)⟩,⟨(-1/2),0,0,(1/6)⟩,⟨(15/34),0,0,(-1/34)⟩⟩⟩

private def sourceBound946 : CertBound := ⟨false,true,⟨⟨(1411141/347800102),(2466337/1043400306),0,0⟩,⟨(19569/54574),(1/54574),0,0⟩,⟨(29714/82849),(-1/82849),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound968 : CertBound := ⟨false,true,⟨⟨(9311221/1158176454),(5424319/1158176454),0,0⟩,⟨(10127/28198),(1/28198),0,0⟩,⟨(4919/13691),(-1/41073),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1003 : CertBound := ⟨false,true,⟨⟨(4537435526450/260705437441007),(29126250350/260705437441007),0,0⟩,⟨(62780/175069),(-1/175069),0,0⟩,⟨(170829/476302),(1/476302),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1013 : CertBound := ⟨false,true,⟨⟨(3023864/142697685),(8765033/1426976850),0,0⟩,⟨(713/1991),(1/5973),0,0⟩,⟨(112/311),(-1/933),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1015 : CertBound := ⟨false,true,⟨⟨(3436033/154937481),(667124/51645827),0,0⟩,⟨(4178/11269),(1/11269),0,0⟩,⟨(1701/4583),(-1/13749),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1024 : CertBound := ⟨false,true,⟨⟨(874485720750/35239157983159),(-35376316250/35239157983159),0,0⟩,⟨(170829/476302),(1/476302),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1041 : CertBound := ⟨false,true,⟨⟨(20528290950/592342509109),(12388023950/65750018511099),0,0⟩,⟨(10689/29759),(-1/89277),0,0⟩,⟨(84635/235558),(1/235558),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1047 : CertBound := ⟨false,true,⟨⟨(1880401/46667049),(365108/15555683),0,0⟩,⟨(735/1991),(1/5973),0,0⟩,⟨(2890/7813),(-1/7813),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1066 : CertBound := ⟨false,true,⟨⟨(427469976750/8363874636247),(-26565444250/8363874636247),0,0⟩,⟨(84635/235558),(1/235558),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1071 : CertBound := ⟨false,true,⟨⟨(1322907/23585446),(2312189/70756338),0,0⟩,⟨(1398/3901),(1/3901),0,0⟩,⟨(2173/6046),(-1/6046),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨2,(-1),0,0⟩⟩⟩

private def sourceBound1088 : CertBound := ⟨false,true,⟨⟨(3187478/35004125),(1328733/70008250),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(616/1657),(-1/1657),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1098 : CertBound := ⟨false,true,⟨⟨(1641924483/15716862500),0,0,(246790851/31433725000)⟩,⟨(1089/2950),0,0,(1/2950)⟩,⟨(3913/10550),0,0,(-1/31650)⟩,⟨(41/166),0,0,(1/166)⟩,⟨(1851/6718),0,0,(-1/6718)⟩⟩⟩

private def sourceBound1118 : CertBound := ⟨false,true,⟨⟨(12740018571/65624465320),(6136962399/1640611633000),0,0⟩,⟨(5491/14843),(1/44529),0,0⟩,⟨(383/1033),(-1/1033),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(1950/7081),(-1/7081),0,0⟩⟩⟩

private def sourceBound1124 : CertBound := ⟨false,true,⟨⟨(17288019/81914300),(23104949/409571500),0,0⟩,⟨(93/262),(1/262),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

private def sourceBound1132 : CertBound := ⟨false,true,⟨⟨(329014964650/1370729503247),(2276619750/1370729503247),0,0⟩,⟨(4519/12598),(-1/12598),0,0⟩,⟨(12510/34801),(1/34801),0,0⟩,⟨(83/313),(1/313),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩

private def sourceBound1138 : CertBound := ⟨false,true,⟨⟨(12374850333/44281430000),0,0,(547966053/44281430000)⟩,⟨(1859/5158),0,0,(1/5158)⟩,⟨(63/170),0,0,(-1/510)⟩,⟨(725/2602),0,0,(1/2602)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩

private def sourceBound1150 : CertBound := ⟨false,true,⟨⟨(33285470319/67820291500),(-327225429/33910145750),0,0⟩,⟨(61/169),(1/169),0,0⟩,⟨(2747/7501),(-1/7501),0,0⟩,⟨(767/2749),(1/2749),0,0⟩,⟨(43/142),(-1/142),0,0⟩⟩⟩

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman
namespace SourceMemo16_76
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,76,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound1013,sourceBound381,sourceBound554,sourceBound1003,sourceBound373,sourceBound524,sourceBound642,sourceBound946,sourceBound130],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound1013,sourceBound381,sourceBound554,sourceBound166,sourceBound612,sourceBound532,sourceBound1024,sourceBound373,sourceBound524,sourceBound642,sourceBound946,sourceBound130],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound175,sourceBound445,sourceBound381,sourceBound554,sourceBound1003,sourceBound373,sourceBound524,sourceBound642,sourceBound946,sourceBound130],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound175,sourceBound445,sourceBound381,sourceBound554,sourceBound166,sourceBound612,sourceBound532,sourceBound1024,sourceBound373,sourceBound524,sourceBound642,sourceBound946,sourceBound130]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound1013,sourceBound381,sourceBound554,sourceBound1003,sourceBound373,sourceBound524,sourceBound642,sourceBound946,sourceBound130].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound1013,sourceBound381,sourceBound554,sourceBound166,sourceBound612,sourceBound532,sourceBound1024,sourceBound373,sourceBound524,sourceBound642,sourceBound946,sourceBound130].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem erase2 : expected[2].eraseDups = expected[2] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[2] (by simp [expected])))
private theorem eraseActual2 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound175,sourceBound445,sourceBound381,sourceBound554,sourceBound1003,sourceBound373,sourceBound524,sourceBound642,sourceBound946,sourceBound130].eraseDups = expected[2] := by
  simpa [expected] using erase2
private theorem erase3 : expected[3].eraseDups = expected[3] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[3] (by simp [expected])))
private theorem eraseActual3 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound175,sourceBound445,sourceBound381,sourceBound554,sourceBound166,sourceBound612,sourceBound532,sourceBound1024,sourceBound373,sourceBound524,sourceBound642,sourceBound946,sourceBound130].eraseDups = expected[3] := by
  simpa [expected] using erase3
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_76.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b20 := sourceBound20) (b21 := sourceBound21) (b42 := sourceBound42) (b43 := sourceBound43) (b130 := sourceBound130) (b166 := sourceBound166) (b175 := sourceBound175) (b260 := sourceBound260) (b371 := sourceBound371) (b373 := sourceBound373) (b381 := sourceBound381) (b421 := sourceBound421) (b440 := sourceBound440) (b445 := sourceBound445) (b524 := sourceBound524) (b532 := sourceBound532) (b554 := sourceBound554) (b612 := sourceBound612) (b642 := sourceBound642) (b692 := sourceBound692) (b795 := sourceBound795) (b806 := sourceBound806) (b824 := sourceBound824) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b946 := sourceBound946) (b1003 := sourceBound1003) (b1013 := sourceBound1013) (b1024 := sourceBound1024) (b1124 := sourceBound1124) (b1138 := sourceBound1138) (b1150 := sourceBound1150)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG4.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG4.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG1.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG1.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG2.1) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pullKey12 BindingNumeric16.pullKey13 BindingNumeric16.pullKey14 BindingNumeric16.norm38 BindingNumeric16.norm10 BindingNumeric16.norm14 BindingNumeric16.pull31 BindingNumeric16.pullKey29 BindingNumeric16.pullKey30 BindingNumeric16.norm15 BindingNumeric16.pullKey31 BindingNumeric16.pull35 BindingNumeric16.pullKey32 BindingNumeric16.pullKey33 BindingNumeric16.pullKey34 BindingNumeric16.norm16 BindingNumeric16.pullKey35 BindingNumeric16.pullKey36 BindingNumeric16.pullKey37 eraseActual0 eraseActual1 eraseActual2 eraseActual3)
end SourceMemo16_76

open Freiman
open Freiman
namespace SourceMemo16_77
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,77,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound169,sourceBound637,sourceBound1041,sourceBound377,sourceBound563,sourceBound690,sourceBound968,sourceBound138],
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound169,sourceBound637,sourceBound194,sourceBound668,sourceBound584,sourceBound1066,sourceBound377,sourceBound563,sourceBound690,sourceBound968,sourceBound138]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound169,sourceBound637,sourceBound1041,sourceBound377,sourceBound563,sourceBound690,sourceBound968,sourceBound138].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem erase1 : expected[1].eraseDups = expected[1] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[1] (by simp [expected])))
private theorem eraseActual1 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound806,sourceBound20,sourceBound795,sourceBound42,sourceBound169,sourceBound637,sourceBound194,sourceBound668,sourceBound584,sourceBound1066,sourceBound377,sourceBound563,sourceBound690,sourceBound968,sourceBound138].eraseDups = expected[1] := by
  simpa [expected] using erase1
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_77.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b20 := sourceBound20) (b21 := sourceBound21) (b42 := sourceBound42) (b43 := sourceBound43) (b138 := sourceBound138) (b169 := sourceBound169) (b194 := sourceBound194) (b260 := sourceBound260) (b371 := sourceBound371) (b377 := sourceBound377) (b421 := sourceBound421) (b440 := sourceBound440) (b563 := sourceBound563) (b584 := sourceBound584) (b637 := sourceBound637) (b668 := sourceBound668) (b690 := sourceBound690) (b692 := sourceBound692) (b795 := sourceBound795) (b806 := sourceBound806) (b824 := sourceBound824) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b968 := sourceBound968) (b1041 := sourceBound1041) (b1066 := sourceBound1066) (b1124 := sourceBound1124) (b1138 := sourceBound1138) (b1150 := sourceBound1150)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG4.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG4.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG1.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG2.2.1) (BindingSourceBranches16.branchesG2.2.2.1) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pullKey12 BindingNumeric16.pullKey13 BindingNumeric16.pullKey14 BindingNumeric16.norm38 BindingNumeric16.norm10 BindingNumeric16.norm14 BindingNumeric16.norm17 BindingNumeric16.pullKey38 BindingNumeric16.pull43 BindingNumeric16.pullKey39 BindingNumeric16.pullKey40 BindingNumeric16.pullKey41 BindingNumeric16.norm18 BindingNumeric16.pullKey42 BindingNumeric16.pullKey43 BindingNumeric16.pullKey44 eraseActual0 eraseActual1)
end SourceMemo16_77

open Freiman
open Freiman
namespace SourceMemo16_78
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,78,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),false),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound263,sourceBound752,sourceBound1132,sourceBound423,sourceBound736,sourceBound809,sourceBound1071,sourceBound262]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound1138,sourceBound1124,sourceBound421,sourceBound692,sourceBound263,sourceBound752,sourceBound1132,sourceBound423,sourceBound736,sourceBound809,sourceBound1071,sourceBound262].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_78.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b21 := sourceBound21) (b43 := sourceBound43) (b260 := sourceBound260) (b262 := sourceBound262) (b263 := sourceBound263) (b371 := sourceBound371) (b421 := sourceBound421) (b423 := sourceBound423) (b440 := sourceBound440) (b692 := sourceBound692) (b736 := sourceBound736) (b752 := sourceBound752) (b809 := sourceBound809) (b824 := sourceBound824) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b1071 := sourceBound1071) (b1124 := sourceBound1124) (b1132 := sourceBound1132) (b1138 := sourceBound1138) (b1150 := sourceBound1150)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG4.2.2.2.2.2.2.1) (BindingSourceBranches16.branchesG5.1) (BindingSourceBranches16.branchesG1.2.1) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pullKey12 BindingNumeric16.pullKey13 BindingNumeric16.pullKey14 BindingNumeric16.norm38 BindingNumeric16.norm8 BindingNumeric16.pullKey15 BindingNumeric16.norm9 BindingNumeric16.pullKey16 BindingNumeric16.pullKey17 BindingNumeric16.pullKey18 eraseActual0)
end SourceMemo16_78

open Freiman
open Freiman
namespace SourceMemo16_79
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,79,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([3],[]),true)],([1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound415,sourceBound726,sourceBound774,sourceBound11,sourceBound789,sourceBound1118,sourceBound1098,sourceBound1088,sourceBound395,sourceBound620,sourceBound753,sourceBound1015,sourceBound183]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound415,sourceBound726,sourceBound774,sourceBound11,sourceBound789,sourceBound1118,sourceBound1098,sourceBound1088,sourceBound395,sourceBound620,sourceBound753,sourceBound1015,sourceBound183].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_79.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b11 := sourceBound11) (b21 := sourceBound21) (b43 := sourceBound43) (b183 := sourceBound183) (b260 := sourceBound260) (b371 := sourceBound371) (b395 := sourceBound395) (b415 := sourceBound415) (b440 := sourceBound440) (b620 := sourceBound620) (b726 := sourceBound726) (b753 := sourceBound753) (b774 := sourceBound774) (b789 := sourceBound789) (b824 := sourceBound824) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b1015 := sourceBound1015) (b1088 := sourceBound1088) (b1098 := sourceBound1098) (b1118 := sourceBound1118) (b1150 := sourceBound1150)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG5.2.1) (BindingSourceBranches16.branchesG5.2.2.1) (BindingSourceBranches16.branchesG2.2.2.2.2.2.2.1) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pullKey12 BindingNumeric16.norm39 BindingNumeric16.norm21 BindingNumeric16.pullKey52 BindingNumeric16.pullKey53 BindingNumeric16.pullKey54 BindingNumeric16.pullKey55 BindingNumeric16.norm22 BindingNumeric16.pullKey56 BindingNumeric16.pullKey57 BindingNumeric16.pullKey58 eraseActual0)
end SourceMemo16_79

open Freiman
open Freiman
namespace SourceMemo16_80
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private def path : LowerHistoryPath := ⟨.left,80,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([2],[]),true)],([1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩
private def expected : List (List CertBound) := [
[sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound415,sourceBound726,sourceBound774,sourceBound11,sourceBound789,sourceBound1118,sourceBound398,sourceBound666,sourceBound786,sourceBound1047,sourceBound197]
]
private theorem fingerprint_nodup :
    ∀ l ∈ expected, (l.map BindingSourceSupport16.fingerprint).Nodup := by
  decide +kernel
private theorem erase0 : expected[0].eraseDups = expected[0] :=
  BindingSourceSupport16.erase_self_of_nodup
    (List.Nodup.of_map BindingSourceSupport16.fingerprint
      (fingerprint_nodup expected[0] (by simp [expected])))
private theorem eraseActual0 : [sourceBound371,sourceBound843,sourceBound260,sourceBound440,sourceBound3,sourceBound856,sourceBound21,sourceBound833,sourceBound43,sourceBound824,sourceBound1150,sourceBound415,sourceBound726,sourceBound774,sourceBound11,sourceBound789,sourceBound1118,sourceBound398,sourceBound666,sourceBound786,sourceBound1047,sourceBound197].eraseDups = expected[0] := by
  simpa [expected] using erase0
private theorem source : lowerHistorySourcePremises path = expected := by
  rw [← RootOps19.actual_eval]
  exact
    (BindingOps16_80.source_structural (ops := RootOps19.actualOps) (b3 := sourceBound3) (b11 := sourceBound11) (b21 := sourceBound21) (b43 := sourceBound43) (b197 := sourceBound197) (b260 := sourceBound260) (b371 := sourceBound371) (b398 := sourceBound398) (b415 := sourceBound415) (b440 := sourceBound440) (b666 := sourceBound666) (b726 := sourceBound726) (b774 := sourceBound774) (b786 := sourceBound786) (b789 := sourceBound789) (b824 := sourceBound824) (b833 := sourceBound833) (b843 := sourceBound843) (b856 := sourceBound856) (b1047 := sourceBound1047) (b1118 := sourceBound1118) (b1150 := sourceBound1150)
      BindingSourceSupport16.relaxed1 BindingNumeric16.initial_base (BindingSourceBranches16.branchesG0.1) (BindingSourceBranches16.branchesG0.2.2.2.2.2.2.2) (BindingSourceBranches16.branchesG5.2.1) (BindingSourceBranches16.branchesG5.2.2.1) (BindingSourceBranches16.branchesG2.2.2.2.2.2.2.2) BindingNumeric16.norm0 BindingNumeric16.norm7 BindingNumeric16.pull11 BindingNumeric16.pullKey12 BindingNumeric16.norm39 BindingNumeric16.norm21 BindingNumeric16.pullKey52 BindingNumeric16.pullKey53 BindingNumeric16.norm23 BindingNumeric16.pullKey59 BindingNumeric16.pullKey60 BindingNumeric16.pullKey61 eraseActual0)
end SourceMemo16_80

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

open Freiman
open Freiman

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
private def path76 : LowerHistoryPath := ⟨.left,76,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([2],[]),true),(([],[1]),false)],([1,2,1,3,1,2,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,4⟩

private theorem records76 : lowerHistoryRecordsFor path76 = [⟨.left,76,0,(-1),false,363,835⟩,⟨.left,76,1,(-1),false,355,835⟩,⟨.left,76,2,(-1),false,359,835⟩,⟨.left,76,3,(-1),false,351,835⟩] := by
  change lowerHistoryRecordsFor (⟨.left,76,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 76, lowerHistoryRecordsL_list] <;> rfl


private def path77 : LowerHistoryPath := ⟨.left,77,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),true),(([1],[]),false),(([1],[]),true),(([],[1]),false)],([1,2,1,3,1,1,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,2⟩

private theorem records77 : lowerHistoryRecordsFor path77 = [⟨.left,77,0,(-1),false,371,865⟩,⟨.left,77,1,(-1),false,367,865⟩] := by
  change lowerHistoryRecordsFor (⟨.left,77,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 77, lowerHistoryRecordsL_list] <;> rfl


private def path78 : LowerHistoryPath := ⟨.left,78,[1],([2],[3]),false,[(([1],[]),false),(([3],[]),true),(([1],[]),false),(([],[1]),false)],([1,2,1,3,1],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩

private theorem records78 : lowerHistoryRecordsFor path78 = [⟨.left,78,0,(-1),false,420,979⟩] := by
  change lowerHistoryRecordsFor (⟨.left,78,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 78, lowerHistoryRecordsL_list] <;> rfl


private def path79 : LowerHistoryPath := ⟨.left,79,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([3],[]),true)],([1,2,1,2,3],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩

private theorem records79 : lowerHistoryRecordsFor path79 = [⟨.left,79,0,(-1),false,326,907⟩] := by
  change lowerHistoryRecordsFor (⟨.left,79,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 79, lowerHistoryRecordsL_list] <;> rfl


private def path80 : LowerHistoryPath := ⟨.left,80,[1],([2],[3]),false,[(([1],[]),false),(([2],[]),true),(([1],[]),true),(([2],[]),true)],([1,2,1,2,2],[3,1,3,1]),(false,false),true,1,⟨(1/2),(4/5),(3/4),(4/5)⟩,1⟩

private theorem records80 : lowerHistoryRecordsFor path80 = [⟨.left,80,0,(-1),false,328,949⟩] := by
  change lowerHistoryRecordsFor (⟨.left,80,[],([],[]),false,[],([],[]),(false,false),false,0,⟨0,0,0,0⟩,0⟩ : LowerHistoryPath) = _
  rw [left_filter 80, lowerHistoryRecordsL_list] <;> rfl


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

private theorem bound371 :
    lowerHistoryBound 371 = sourceBound371 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[170]? = some sourceBound371 :=
    Eq.refl (some sourceBound371)
  exact (BoundCompact16.global_to_chunk2 170 (by decide)).trans hlocal

private theorem bound423 :
    lowerHistoryBound 423 = sourceBound423 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[22]? = some sourceBound423 :=
    Eq.refl (some sourceBound423)
  exact (BoundCompact16.global_to_chunk3 22 (by decide)).trans hlocal

private theorem bound440 :
    lowerHistoryBound 440 = sourceBound440 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[39]? = some sourceBound440 :=
    Eq.refl (some sourceBound440)
  exact (BoundCompact16.global_to_chunk3 39 (by decide)).trans hlocal

private theorem bound736 :
    lowerHistoryBound 736 = sourceBound736 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[135]? = some sourceBound736 :=
    Eq.refl (some sourceBound736)
  exact (BoundCompact16.global_to_chunk4 135 (by decide)).trans hlocal

private theorem bound752 :
    lowerHistoryBound 752 = sourceBound752 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[151]? = some sourceBound752 :=
    Eq.refl (some sourceBound752)
  exact (BoundCompact16.global_to_chunk4 151 (by decide)).trans hlocal

private theorem bound809 :
    lowerHistoryBound 809 = sourceBound809 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[8]? = some sourceBound809 :=
    Eq.refl (some sourceBound809)
  exact (BoundCompact16.global_to_chunk5 8 (by decide)).trans hlocal

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

private theorem bound1071 :
    lowerHistoryBound 1071 = sourceBound1071 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[70]? = some sourceBound1071 :=
    Eq.refl (some sourceBound1071)
  exact (BoundCompact16.global_to_chunk6 70).trans hlocal

private theorem bound1132 :
    lowerHistoryBound 1132 = sourceBound1132 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[131]? = some sourceBound1132 :=
    Eq.refl (some sourceBound1132)
  exact (BoundCompact16.global_to_chunk6 131).trans hlocal

end BatchLookup15

namespace BatchLookup16
open Freiman

private theorem bound11 :
    lowerHistoryBound 11 = sourceBound11 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[10]? = some sourceBound11 :=
    Eq.refl (some sourceBound11)
  exact (BoundCompact16.global_to_chunk1 10 (by decide)).trans hlocal

private theorem bound20 :
    lowerHistoryBound 20 = sourceBound20 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[19]? = some sourceBound20 :=
    Eq.refl (some sourceBound20)
  exact (BoundCompact16.global_to_chunk1 19 (by decide)).trans hlocal

private theorem bound42 :
    lowerHistoryBound 42 = sourceBound42 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[41]? = some sourceBound42 :=
    Eq.refl (some sourceBound42)
  exact (BoundCompact16.global_to_chunk1 41 (by decide)).trans hlocal

private theorem bound43 :
    lowerHistoryBound 43 = sourceBound43 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[42]? = some sourceBound43 :=
    Eq.refl (some sourceBound43)
  exact (BoundCompact16.global_to_chunk1 42 (by decide)).trans hlocal

private theorem bound130 :
    lowerHistoryBound 130 = sourceBound130 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[129]? = some sourceBound130 :=
    Eq.refl (some sourceBound130)
  exact (BoundCompact16.global_to_chunk1 129 (by decide)).trans hlocal

private theorem bound138 :
    lowerHistoryBound 138 = sourceBound138 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[137]? = some sourceBound138 :=
    Eq.refl (some sourceBound138)
  exact (BoundCompact16.global_to_chunk1 137 (by decide)).trans hlocal

private theorem bound166 :
    lowerHistoryBound 166 = sourceBound166 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[165]? = some sourceBound166 :=
    Eq.refl (some sourceBound166)
  exact (BoundCompact16.global_to_chunk1 165 (by decide)).trans hlocal

private theorem bound169 :
    lowerHistoryBound 169 = sourceBound169 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[168]? = some sourceBound169 :=
    Eq.refl (some sourceBound169)
  exact (BoundCompact16.global_to_chunk1 168 (by decide)).trans hlocal

private theorem bound175 :
    lowerHistoryBound 175 = sourceBound175 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[174]? = some sourceBound175 :=
    Eq.refl (some sourceBound175)
  exact (BoundCompact16.global_to_chunk1 174 (by decide)).trans hlocal

private theorem bound183 :
    lowerHistoryBound 183 = sourceBound183 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[182]? = some sourceBound183 :=
    Eq.refl (some sourceBound183)
  exact (BoundCompact16.global_to_chunk1 182 (by decide)).trans hlocal

private theorem bound194 :
    lowerHistoryBound 194 = sourceBound194 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[193]? = some sourceBound194 :=
    Eq.refl (some sourceBound194)
  exact (BoundCompact16.global_to_chunk1 193 (by decide)).trans hlocal

private theorem bound197 :
    lowerHistoryBound 197 = sourceBound197 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds01[196]? = some sourceBound197 :=
    Eq.refl (some sourceBound197)
  exact (BoundCompact16.global_to_chunk1 196 (by decide)).trans hlocal

private theorem bound263 :
    lowerHistoryBound 263 = sourceBound263 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[62]? = some sourceBound263 :=
    Eq.refl (some sourceBound263)
  exact (BoundCompact16.global_to_chunk2 62 (by decide)).trans hlocal

private theorem bound373 :
    lowerHistoryBound 373 = sourceBound373 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[172]? = some sourceBound373 :=
    Eq.refl (some sourceBound373)
  exact (BoundCompact16.global_to_chunk2 172 (by decide)).trans hlocal

private theorem bound377 :
    lowerHistoryBound 377 = sourceBound377 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[176]? = some sourceBound377 :=
    Eq.refl (some sourceBound377)
  exact (BoundCompact16.global_to_chunk2 176 (by decide)).trans hlocal

private theorem bound381 :
    lowerHistoryBound 381 = sourceBound381 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds02[180]? = some sourceBound381 :=
    Eq.refl (some sourceBound381)
  exact (BoundCompact16.global_to_chunk2 180 (by decide)).trans hlocal

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

private theorem bound415 :
    lowerHistoryBound 415 = sourceBound415 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[14]? = some sourceBound415 :=
    Eq.refl (some sourceBound415)
  exact (BoundCompact16.global_to_chunk3 14 (by decide)).trans hlocal

private theorem bound421 :
    lowerHistoryBound 421 = sourceBound421 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[20]? = some sourceBound421 :=
    Eq.refl (some sourceBound421)
  exact (BoundCompact16.global_to_chunk3 20 (by decide)).trans hlocal

private theorem bound445 :
    lowerHistoryBound 445 = sourceBound445 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[44]? = some sourceBound445 :=
    Eq.refl (some sourceBound445)
  exact (BoundCompact16.global_to_chunk3 44 (by decide)).trans hlocal

private theorem bound524 :
    lowerHistoryBound 524 = sourceBound524 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[123]? = some sourceBound524 :=
    Eq.refl (some sourceBound524)
  exact (BoundCompact16.global_to_chunk3 123 (by decide)).trans hlocal

private theorem bound532 :
    lowerHistoryBound 532 = sourceBound532 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[131]? = some sourceBound532 :=
    Eq.refl (some sourceBound532)
  exact (BoundCompact16.global_to_chunk3 131 (by decide)).trans hlocal

private theorem bound554 :
    lowerHistoryBound 554 = sourceBound554 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[153]? = some sourceBound554 :=
    Eq.refl (some sourceBound554)
  exact (BoundCompact16.global_to_chunk3 153 (by decide)).trans hlocal

private theorem bound563 :
    lowerHistoryBound 563 = sourceBound563 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[162]? = some sourceBound563 :=
    Eq.refl (some sourceBound563)
  exact (BoundCompact16.global_to_chunk3 162 (by decide)).trans hlocal

private theorem bound584 :
    lowerHistoryBound 584 = sourceBound584 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds03[183]? = some sourceBound584 :=
    Eq.refl (some sourceBound584)
  exact (BoundCompact16.global_to_chunk3 183 (by decide)).trans hlocal

private theorem bound612 :
    lowerHistoryBound 612 = sourceBound612 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[11]? = some sourceBound612 :=
    Eq.refl (some sourceBound612)
  exact (BoundCompact16.global_to_chunk4 11 (by decide)).trans hlocal

private theorem bound620 :
    lowerHistoryBound 620 = sourceBound620 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[19]? = some sourceBound620 :=
    Eq.refl (some sourceBound620)
  exact (BoundCompact16.global_to_chunk4 19 (by decide)).trans hlocal

private theorem bound637 :
    lowerHistoryBound 637 = sourceBound637 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[36]? = some sourceBound637 :=
    Eq.refl (some sourceBound637)
  exact (BoundCompact16.global_to_chunk4 36 (by decide)).trans hlocal

private theorem bound642 :
    lowerHistoryBound 642 = sourceBound642 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[41]? = some sourceBound642 :=
    Eq.refl (some sourceBound642)
  exact (BoundCompact16.global_to_chunk4 41 (by decide)).trans hlocal

private theorem bound666 :
    lowerHistoryBound 666 = sourceBound666 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[65]? = some sourceBound666 :=
    Eq.refl (some sourceBound666)
  exact (BoundCompact16.global_to_chunk4 65 (by decide)).trans hlocal

private theorem bound668 :
    lowerHistoryBound 668 = sourceBound668 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[67]? = some sourceBound668 :=
    Eq.refl (some sourceBound668)
  exact (BoundCompact16.global_to_chunk4 67 (by decide)).trans hlocal

private theorem bound690 :
    lowerHistoryBound 690 = sourceBound690 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[89]? = some sourceBound690 :=
    Eq.refl (some sourceBound690)
  exact (BoundCompact16.global_to_chunk4 89 (by decide)).trans hlocal

private theorem bound692 :
    lowerHistoryBound 692 = sourceBound692 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[91]? = some sourceBound692 :=
    Eq.refl (some sourceBound692)
  exact (BoundCompact16.global_to_chunk4 91 (by decide)).trans hlocal

private theorem bound726 :
    lowerHistoryBound 726 = sourceBound726 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[125]? = some sourceBound726 :=
    Eq.refl (some sourceBound726)
  exact (BoundCompact16.global_to_chunk4 125 (by decide)).trans hlocal

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

private theorem bound795 :
    lowerHistoryBound 795 = sourceBound795 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds04[194]? = some sourceBound795 :=
    Eq.refl (some sourceBound795)
  exact (BoundCompact16.global_to_chunk4 194 (by decide)).trans hlocal

private theorem bound806 :
    lowerHistoryBound 806 = sourceBound806 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[5]? = some sourceBound806 :=
    Eq.refl (some sourceBound806)
  exact (BoundCompact16.global_to_chunk5 5 (by decide)).trans hlocal

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

private theorem bound946 :
    lowerHistoryBound 946 = sourceBound946 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[145]? = some sourceBound946 :=
    Eq.refl (some sourceBound946)
  exact (BoundCompact16.global_to_chunk5 145 (by decide)).trans hlocal

private theorem bound968 :
    lowerHistoryBound 968 = sourceBound968 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds05[167]? = some sourceBound968 :=
    Eq.refl (some sourceBound968)
  exact (BoundCompact16.global_to_chunk5 167 (by decide)).trans hlocal

private theorem bound1003 :
    lowerHistoryBound 1003 = sourceBound1003 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[2]? = some sourceBound1003 :=
    Eq.refl (some sourceBound1003)
  exact (BoundCompact16.global_to_chunk6 2).trans hlocal

private theorem bound1013 :
    lowerHistoryBound 1013 = sourceBound1013 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[12]? = some sourceBound1013 :=
    Eq.refl (some sourceBound1013)
  exact (BoundCompact16.global_to_chunk6 12).trans hlocal

private theorem bound1015 :
    lowerHistoryBound 1015 = sourceBound1015 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[14]? = some sourceBound1015 :=
    Eq.refl (some sourceBound1015)
  exact (BoundCompact16.global_to_chunk6 14).trans hlocal

private theorem bound1024 :
    lowerHistoryBound 1024 = sourceBound1024 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[23]? = some sourceBound1024 :=
    Eq.refl (some sourceBound1024)
  exact (BoundCompact16.global_to_chunk6 23).trans hlocal

private theorem bound1041 :
    lowerHistoryBound 1041 = sourceBound1041 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[40]? = some sourceBound1041 :=
    Eq.refl (some sourceBound1041)
  exact (BoundCompact16.global_to_chunk6 40).trans hlocal

private theorem bound1047 :
    lowerHistoryBound 1047 = sourceBound1047 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[46]? = some sourceBound1047 :=
    Eq.refl (some sourceBound1047)
  exact (BoundCompact16.global_to_chunk6 46).trans hlocal

private theorem bound1066 :
    lowerHistoryBound 1066 = sourceBound1066 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[65]? = some sourceBound1066 :=
    Eq.refl (some sourceBound1066)
  exact (BoundCompact16.global_to_chunk6 65).trans hlocal

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

private theorem bound1124 :
    lowerHistoryBound 1124 = sourceBound1124 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[123]? = some sourceBound1124 :=
    Eq.refl (some sourceBound1124)
  exact (BoundCompact16.global_to_chunk6 123).trans hlocal

private theorem bound1138 :
    lowerHistoryBound 1138 = sourceBound1138 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[137]? = some sourceBound1138 :=
    Eq.refl (some sourceBound1138)
  exact (BoundCompact16.global_to_chunk6 137).trans hlocal

private theorem bound1150 :
    lowerHistoryBound 1150 = sourceBound1150 := by
  apply BoundCompact16.bound_of_option
  have hlocal : lowerHistoryBounds06[149]? = some sourceBound1150 :=
    Eq.refl (some sourceBound1150)
  exact (BoundCompact16.global_to_chunk6 149).trans hlocal

end BatchLookup16


-- Source: agents.batch16.SourceValuesAll
open Freiman
namespace SourceValues16
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
private theorem source76 : lowerHistorySourcePremises BatchLookup16.path76 =
    ([[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,1013,381,554,1003,373,524,642,946,130],[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,1013,381,554,166,612,532,1024,373,524,642,946,130],[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,175,445,381,554,1003,373,524,642,946,130],[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,175,445,381,554,166,612,532,1024,373,524,642,946,130]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound1150 (congrArg₂ List.cons BatchLookup16.bound1138 (congrArg₂ List.cons BatchLookup16.bound1124 (congrArg₂ List.cons BatchLookup16.bound421 (congrArg₂ List.cons BatchLookup16.bound692 (congrArg₂ List.cons BatchLookup16.bound806 (congrArg₂ List.cons BatchLookup16.bound20 (congrArg₂ List.cons BatchLookup16.bound795 (congrArg₂ List.cons BatchLookup16.bound42 (congrArg₂ List.cons BatchLookup16.bound1013 (congrArg₂ List.cons BatchLookup16.bound381 (congrArg₂ List.cons BatchLookup16.bound554 (congrArg₂ List.cons BatchLookup16.bound1003 (congrArg₂ List.cons BatchLookup16.bound373 (congrArg₂ List.cons BatchLookup16.bound524 (congrArg₂ List.cons BatchLookup16.bound642 (congrArg₂ List.cons BatchLookup16.bound946 (congrArg₂ List.cons BatchLookup16.bound130 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound1150 (congrArg₂ List.cons BatchLookup16.bound1138 (congrArg₂ List.cons BatchLookup16.bound1124 (congrArg₂ List.cons BatchLookup16.bound421 (congrArg₂ List.cons BatchLookup16.bound692 (congrArg₂ List.cons BatchLookup16.bound806 (congrArg₂ List.cons BatchLookup16.bound20 (congrArg₂ List.cons BatchLookup16.bound795 (congrArg₂ List.cons BatchLookup16.bound42 (congrArg₂ List.cons BatchLookup16.bound1013 (congrArg₂ List.cons BatchLookup16.bound381 (congrArg₂ List.cons BatchLookup16.bound554 (congrArg₂ List.cons BatchLookup16.bound166 (congrArg₂ List.cons BatchLookup16.bound612 (congrArg₂ List.cons BatchLookup16.bound532 (congrArg₂ List.cons BatchLookup16.bound1024 (congrArg₂ List.cons BatchLookup16.bound373 (congrArg₂ List.cons BatchLookup16.bound524 (congrArg₂ List.cons BatchLookup16.bound642 (congrArg₂ List.cons BatchLookup16.bound946 (congrArg₂ List.cons BatchLookup16.bound130 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound1150 (congrArg₂ List.cons BatchLookup16.bound1138 (congrArg₂ List.cons BatchLookup16.bound1124 (congrArg₂ List.cons BatchLookup16.bound421 (congrArg₂ List.cons BatchLookup16.bound692 (congrArg₂ List.cons BatchLookup16.bound806 (congrArg₂ List.cons BatchLookup16.bound20 (congrArg₂ List.cons BatchLookup16.bound795 (congrArg₂ List.cons BatchLookup16.bound42 (congrArg₂ List.cons BatchLookup16.bound175 (congrArg₂ List.cons BatchLookup16.bound445 (congrArg₂ List.cons BatchLookup16.bound381 (congrArg₂ List.cons BatchLookup16.bound554 (congrArg₂ List.cons BatchLookup16.bound1003 (congrArg₂ List.cons BatchLookup16.bound373 (congrArg₂ List.cons BatchLookup16.bound524 (congrArg₂ List.cons BatchLookup16.bound642 (congrArg₂ List.cons BatchLookup16.bound946 (congrArg₂ List.cons BatchLookup16.bound130 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound1150 (congrArg₂ List.cons BatchLookup16.bound1138 (congrArg₂ List.cons BatchLookup16.bound1124 (congrArg₂ List.cons BatchLookup16.bound421 (congrArg₂ List.cons BatchLookup16.bound692 (congrArg₂ List.cons BatchLookup16.bound806 (congrArg₂ List.cons BatchLookup16.bound20 (congrArg₂ List.cons BatchLookup16.bound795 (congrArg₂ List.cons BatchLookup16.bound42 (congrArg₂ List.cons BatchLookup16.bound175 (congrArg₂ List.cons BatchLookup16.bound445 (congrArg₂ List.cons BatchLookup16.bound381 (congrArg₂ List.cons BatchLookup16.bound554 (congrArg₂ List.cons BatchLookup16.bound166 (congrArg₂ List.cons BatchLookup16.bound612 (congrArg₂ List.cons BatchLookup16.bound532 (congrArg₂ List.cons BatchLookup16.bound1024 (congrArg₂ List.cons BatchLookup16.bound373 (congrArg₂ List.cons BatchLookup16.bound524 (congrArg₂ List.cons BatchLookup16.bound642 (congrArg₂ List.cons BatchLookup16.bound946 (congrArg₂ List.cons BatchLookup16.bound130 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))))
  exact SourceMemo16_76.source.trans hb.symm
private theorem length76 : BatchLookup16.path76.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path76).length := by
  exact (congrArg List.length source76).symm
private theorem source77 : lowerHistorySourcePremises BatchLookup16.path77 =
    ([[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,169,637,1041,377,563,690,968,138],[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,169,637,194,668,584,1066,377,563,690,968,138]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound1150 (congrArg₂ List.cons BatchLookup16.bound1138 (congrArg₂ List.cons BatchLookup16.bound1124 (congrArg₂ List.cons BatchLookup16.bound421 (congrArg₂ List.cons BatchLookup16.bound692 (congrArg₂ List.cons BatchLookup16.bound806 (congrArg₂ List.cons BatchLookup16.bound20 (congrArg₂ List.cons BatchLookup16.bound795 (congrArg₂ List.cons BatchLookup16.bound42 (congrArg₂ List.cons BatchLookup16.bound169 (congrArg₂ List.cons BatchLookup16.bound637 (congrArg₂ List.cons BatchLookup16.bound1041 (congrArg₂ List.cons BatchLookup16.bound377 (congrArg₂ List.cons BatchLookup16.bound563 (congrArg₂ List.cons BatchLookup16.bound690 (congrArg₂ List.cons BatchLookup16.bound968 (congrArg₂ List.cons BatchLookup16.bound138 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))))))) (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound1150 (congrArg₂ List.cons BatchLookup16.bound1138 (congrArg₂ List.cons BatchLookup16.bound1124 (congrArg₂ List.cons BatchLookup16.bound421 (congrArg₂ List.cons BatchLookup16.bound692 (congrArg₂ List.cons BatchLookup16.bound806 (congrArg₂ List.cons BatchLookup16.bound20 (congrArg₂ List.cons BatchLookup16.bound795 (congrArg₂ List.cons BatchLookup16.bound42 (congrArg₂ List.cons BatchLookup16.bound169 (congrArg₂ List.cons BatchLookup16.bound637 (congrArg₂ List.cons BatchLookup16.bound194 (congrArg₂ List.cons BatchLookup16.bound668 (congrArg₂ List.cons BatchLookup16.bound584 (congrArg₂ List.cons BatchLookup16.bound1066 (congrArg₂ List.cons BatchLookup16.bound377 (congrArg₂ List.cons BatchLookup16.bound563 (congrArg₂ List.cons BatchLookup16.bound690 (congrArg₂ List.cons BatchLookup16.bound968 (congrArg₂ List.cons BatchLookup16.bound138 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = [])))
  exact SourceMemo16_77.source.trans hb.symm
private theorem length77 : BatchLookup16.path77.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path77).length := by
  exact (congrArg List.length source77).symm
private theorem source78 : lowerHistorySourcePremises BatchLookup16.path78 =
    ([[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,263,752,1132,423,736,809,1071,262]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound1150 (congrArg₂ List.cons BatchLookup16.bound1138 (congrArg₂ List.cons BatchLookup16.bound1124 (congrArg₂ List.cons BatchLookup16.bound421 (congrArg₂ List.cons BatchLookup16.bound692 (congrArg₂ List.cons BatchLookup16.bound263 (congrArg₂ List.cons BatchLookup15.bound752 (congrArg₂ List.cons BatchLookup15.bound1132 (congrArg₂ List.cons BatchLookup15.bound423 (congrArg₂ List.cons BatchLookup15.bound736 (congrArg₂ List.cons BatchLookup15.bound809 (congrArg₂ List.cons BatchLookup15.bound1071 (congrArg₂ List.cons BatchLookup15.bound262 (rfl : ([] : List CertBound) = [])))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo16_78.source.trans hb.symm
private theorem length78 : BatchLookup16.path78.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path78).length := by
  exact (congrArg List.length source78).symm
private theorem source79 : lowerHistorySourcePremises BatchLookup16.path79 =
    ([[371,843,260,440,3,856,21,833,43,824,1150,415,726,774,11,789,1118,1098,1088,395,620,753,1015,183]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound1150 (congrArg₂ List.cons BatchLookup16.bound415 (congrArg₂ List.cons BatchLookup16.bound726 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup16.bound789 (congrArg₂ List.cons BatchLookup16.bound1118 (congrArg₂ List.cons BatchLookup16.bound1098 (congrArg₂ List.cons BatchLookup16.bound1088 (congrArg₂ List.cons BatchLookup16.bound395 (congrArg₂ List.cons BatchLookup16.bound620 (congrArg₂ List.cons BatchLookup16.bound753 (congrArg₂ List.cons BatchLookup16.bound1015 (congrArg₂ List.cons BatchLookup16.bound183 (rfl : ([] : List CertBound) = []))))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo16_79.source.trans hb.symm
private theorem length79 : BatchLookup16.path79.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path79).length := by
  exact (congrArg List.length source79).symm
private theorem source80 : lowerHistorySourcePremises BatchLookup16.path80 =
    ([[371,843,260,440,3,856,21,833,43,824,1150,415,726,774,11,789,1118,398,666,786,1047,197]] : List (List Nat)).map (List.map lowerHistoryBound) := by
  have hb := (congrArg₂ List.cons (congrArg₂ List.cons BatchLookup15.bound371 (congrArg₂ List.cons BatchLookup15.bound843 (congrArg₂ List.cons BatchLookup15.bound260 (congrArg₂ List.cons BatchLookup15.bound440 (congrArg₂ List.cons BatchLookup15.bound3 (congrArg₂ List.cons BatchLookup15.bound856 (congrArg₂ List.cons BatchLookup15.bound21 (congrArg₂ List.cons BatchLookup16.bound833 (congrArg₂ List.cons BatchLookup16.bound43 (congrArg₂ List.cons BatchLookup16.bound824 (congrArg₂ List.cons BatchLookup16.bound1150 (congrArg₂ List.cons BatchLookup16.bound415 (congrArg₂ List.cons BatchLookup16.bound726 (congrArg₂ List.cons BatchLookup16.bound774 (congrArg₂ List.cons BatchLookup16.bound11 (congrArg₂ List.cons BatchLookup16.bound789 (congrArg₂ List.cons BatchLookup16.bound1118 (congrArg₂ List.cons BatchLookup16.bound398 (congrArg₂ List.cons BatchLookup16.bound666 (congrArg₂ List.cons BatchLookup16.bound786 (congrArg₂ List.cons BatchLookup16.bound1047 (congrArg₂ List.cons BatchLookup16.bound197 (rfl : ([] : List CertBound) = []))))))))))))))))))))))) (rfl : ([] : List (List CertBound)) = []))
  exact SourceMemo16_80.source.trans hb.symm
private theorem length80 : BatchLookup16.path80.alternatives =
    (lowerHistorySourcePremises BatchLookup16.path80).length := by
  exact (congrArg List.length source80).symm
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
private theorem premise326 : lowerHistoryPremises[325]? = some ([3, 11, 21, 43, 183, 260, 371, 395, 415, 440, 620, 726, 753, 774, 789, 824, 833, 843, 856, 1015, 1088, 1098, 1118, 1150] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 325 = 200+125 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 125 (by decide)]
  rfl

private theorem premise328 : lowerHistoryPremises[327]? = some ([3, 11, 21, 43, 197, 260, 371, 398, 415, 440, 666, 726, 774, 786, 789, 824, 833, 843, 856, 1047, 1118, 1150] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 327 = 200+127 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 127 (by decide)]
  rfl

private theorem premise351 : lowerHistoryPremises[350]? = some ([3, 20, 21, 42, 43, 130, 166, 175, 260, 371, 373, 381, 421, 440, 445, 524, 532, 554, 612, 642, 692, 795, 806, 824, 833, 843, 856, 946, 1024, 1124, 1138, 1150] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 350 = 200+150 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 150 (by decide)]
  rfl

private theorem premise355 : lowerHistoryPremises[354]? = some ([3, 20, 21, 42, 43, 130, 166, 260, 371, 373, 381, 421, 440, 524, 532, 554, 612, 642, 692, 795, 806, 824, 833, 843, 856, 946, 1013, 1024, 1124, 1138, 1150] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 354 = 200+154 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 154 (by decide)]
  rfl

private theorem premise359 : lowerHistoryPremises[358]? = some ([3, 20, 21, 42, 43, 130, 175, 260, 371, 373, 381, 421, 440, 445, 524, 554, 642, 692, 795, 806, 824, 833, 843, 856, 946, 1003, 1124, 1138, 1150] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 358 = 200+158 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 158 (by decide)]
  rfl

private theorem premise363 : lowerHistoryPremises[362]? = some ([3, 20, 21, 42, 43, 130, 260, 371, 373, 381, 421, 440, 524, 554, 642, 692, 795, 806, 824, 833, 843, 856, 946, 1003, 1013, 1124, 1138, 1150] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 362 = 200+162 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 162 (by decide)]
  rfl

private theorem premise367 : lowerHistoryPremises[366]? = some ([3, 20, 21, 42, 43, 138, 169, 194, 260, 371, 377, 421, 440, 563, 584, 637, 668, 690, 692, 795, 806, 824, 833, 843, 856, 968, 1066, 1124, 1138, 1150] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 366 = 200+166 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 166 (by decide)]
  rfl

private theorem premise371 : lowerHistoryPremises[370]? = some ([3, 20, 21, 42, 43, 138, 169, 260, 371, 377, 421, 440, 563, 637, 690, 692, 795, 806, 824, 833, 843, 856, 968, 1041, 1124, 1138, 1150] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 370 = 200+170 by decide]
  rw [PremiseCompact50.lookup_chunk2 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 170 (by decide)]
  rfl

private theorem premise420 : lowerHistoryPremises[419]? = some ([3, 21, 43, 260, 262, 263, 371, 421, 423, 440, 692, 736, 752, 809, 824, 833, 843, 856, 1071, 1124, 1132, 1138, 1150] : List ℕ) := by
  unfold lowerHistoryPremises
  rw [show 419 = 400+19 by decide]
  rw [PremiseCompact50.lookup_chunk3 lowerHistoryPremises01 lowerHistoryPremises02 lowerHistoryPremises03 lowerHistoryPremises04 lowerHistoryPremises05 lowerHistoryPremises06 size01 size02 size03 size04 size05 19 (by decide)]
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
private theorem coverage76 : (List.range path76.alternatives).all
    (coverageCheck path76 ([⟨.left,76,0,(-1),false,363,835⟩,⟨.left,76,1,(-1),false,355,835⟩,⟨.left,76,2,(-1),false,359,835⟩,⟨.left,76,3,(-1),false,351,835⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage77 : (List.range path77.alternatives).all
    (coverageCheck path77 ([⟨.left,77,0,(-1),false,371,865⟩,⟨.left,77,1,(-1),false,367,865⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage78 : (List.range path78.alternatives).all
    (coverageCheck path78 ([⟨.left,78,0,(-1),false,420,979⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage79 : (List.range path79.alternatives).all
    (coverageCheck path79 ([⟨.left,79,0,(-1),false,326,907⟩] : List LowerHistoryRecord)) = true := by
  exact Eq.refl (true)
private theorem coverage80 : (List.range path80.alternatives).all
    (coverageCheck path80 ([⟨.left,80,0,(-1),false,328,949⟩] : List LowerHistoryRecord)) = true := by
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
private theorem path76_lookup : lowerHistoryPaths[75]? = some path76 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[25]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[75]? = some path76 :=
    (slice_get lowerHistoryPathsL.toList 25 (by decide)).symm.trans hs
  exact (first_lookup 75 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path77_lookup : lowerHistoryPaths[76]? = some path77 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[26]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[76]? = some path77 :=
    (slice_get lowerHistoryPathsL.toList 26 (by decide)).symm.trans hs
  exact (first_lookup 76 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path78_lookup : lowerHistoryPaths[77]? = some path78 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[27]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[77]? = some path78 :=
    (slice_get lowerHistoryPathsL.toList 27 (by decide)).symm.trans hs
  exact (first_lookup 77 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path79_lookup : lowerHistoryPaths[78]? = some path79 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[28]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[78]? = some path79 :=
    (slice_get lowerHistoryPathsL.toList 28 (by decide)).symm.trans hs
  exact (first_lookup 78 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
private theorem path80_lookup : lowerHistoryPaths[79]? = some path80 := by
  have hs := congrArg (fun xs : List LowerHistoryPath => xs[29]?) pathsL_slice
  have hl : lowerHistoryPathsL.toList[79]? = some path80 :=
    (slice_get lowerHistoryPathsL.toList 29 (by decide)).symm.trans hs
  exact (first_lookup 79 (by decide)).trans (Array.getElem?_toList.symm.trans hl)
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

private theorem witness979_projection :
    (lowerHistoryWitness 979).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 979).upperBound = lowerHistoryBound 1071 ∧
    (lowerHistoryWitness 979).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[178]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 1071, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 1071, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk5 178 (by decide))).trans hl

end WitnessLookup15

namespace WitnessLookup16
open Freiman

private theorem witness835_projection :
    (lowerHistoryWitness 835).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 835).upperBound = lowerHistoryBound 946 ∧
    (lowerHistoryWitness 835).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[34]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 946, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 946, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk5 34 (by decide))).trans hl

private theorem witness865_projection :
    (lowerHistoryWitness 865).lowerBound = lowerHistoryBound 440 ∧
    (lowerHistoryWitness 865).upperBound = lowerHistoryBound 968 ∧
    (lowerHistoryWitness 865).rectangle = (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle) := by
  apply WitnessCompact16.projection_of_global_option
  have hl : (lowerHistoryWitnesses05[64]?).map WitnessCompact16.witnessShape = some (lowerHistoryBound 440, lowerHistoryBound 968, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)) :=
    Eq.refl (some (lowerHistoryBound 440, lowerHistoryBound 968, (⟨(1/2),(4/5),(3/4),(4/5)⟩ : CertRectangle)))
  exact (congrArg (Option.map WitnessCompact16.witnessShape)
    (WitnessCompact16.global_to_chunk5 64 (by decide))).trans hl

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
private def src76 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,1013,381,554,1003,373,524,642,946,130],[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,1013,381,554,166,612,532,1024,373,524,642,946,130],[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,175,445,381,554,1003,373,524,642,946,130],[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,175,445,381,554,166,612,532,1024,373,524,642,946,130]]
private def recs76 : List LowerHistoryRecord := [⟨.left,76,0,(-1),false,363,835⟩,⟨.left,76,1,(-1),false,355,835⟩,⟨.left,76,2,(-1),false,359,835⟩,⟨.left,76,3,(-1),false,351,835⟩]
private theorem check76 : recs76.all (recordCheck path76 src76 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path76_binding : lowerHistoryPathBinding path76 := by
  apply pathBinding_from_ids path76 src76 [] recs76 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source76 rfl records76 rfl
  · intro r hr _
    simp only [recs76, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise363)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise355)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise359)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise351)
  · intro r hr _
    simp only [recs76, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [wids, path76] using WitnessLookup16.witness835_projection
    · simpa only [wids, path76] using WitnessLookup16.witness835_projection
    · simpa only [wids, path76] using WitnessLookup16.witness835_projection
    · simpa only [wids, path76] using WitnessLookup16.witness835_projection
  · exact check76
  · exact BatchCoverage15.coverage_sound path76 recs76
      records76 SourceValues16.length76 BatchCoverageAll16.coverage76
private def src77 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,169,637,1041,377,563,690,968,138],[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,806,20,795,42,169,637,194,668,584,1066,377,563,690,968,138]]
private def recs77 : List LowerHistoryRecord := [⟨.left,77,0,(-1),false,371,865⟩,⟨.left,77,1,(-1),false,367,865⟩]
private theorem check77 : recs77.all (recordCheck path77 src77 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path77_binding : lowerHistoryPathBinding path77 := by
  apply pathBinding_from_ids path77 src77 [] recs77 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source77 rfl records77 rfl
  · intro r hr _
    simp only [recs77, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise371)
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise367)
  · intro r hr _
    simp only [recs77, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simpa only [wids, path77] using WitnessLookup16.witness865_projection
    · simpa only [wids, path77] using WitnessLookup16.witness865_projection
  · exact check77
  · exact BatchCoverage15.coverage_sound path77 recs77
      records77 SourceValues16.length77 BatchCoverageAll16.coverage77
private def src78 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,1150,1138,1124,421,692,263,752,1132,423,736,809,1071,262]]
private def recs78 : List LowerHistoryRecord := [⟨.left,78,0,(-1),false,420,979⟩]
private theorem check78 : recs78.all (recordCheck path78 src78 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path78_binding : lowerHistoryPathBinding path78 := by
  apply pathBinding_from_ids path78 src78 [] recs78 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source78 rfl records78 rfl
  · intro r hr _
    simp only [recs78, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise420)
  · intro r hr _
    simp only [recs78, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path78] using WitnessLookup15.witness979_projection
  · exact check78
  · exact BatchCoverage15.coverage_sound path78 recs78
      records78 SourceValues16.length78 BatchCoverageAll16.coverage78
private def src79 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,1150,415,726,774,11,789,1118,1098,1088,395,620,753,1015,183]]
private def recs79 : List LowerHistoryRecord := [⟨.left,79,0,(-1),false,326,907⟩]
private theorem check79 : recs79.all (recordCheck path79 src79 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path79_binding : lowerHistoryPathBinding path79 := by
  apply pathBinding_from_ids path79 src79 [] recs79 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source79 rfl records79 rfl
  · intro r hr _
    simp only [recs79, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise326)
  · intro r hr _
    simp only [recs79, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path79] using WitnessLookup16.witness907_projection
  · exact check79
  · exact BatchCoverage15.coverage_sound path79 recs79
      records79 SourceValues16.length79 BatchCoverageAll16.coverage79
private def src80 : List (List Nat) := [[371,843,260,440,3,856,21,833,43,824,1150,415,726,774,11,789,1118,398,666,786,1047,197]]
private def recs80 : List LowerHistoryRecord := [⟨.left,80,0,(-1),false,328,949⟩]
private theorem check80 : recs80.all (recordCheck path80 src80 [] wids preIDs 1025 1194) = true := by
  decide +kernel
private theorem path80_binding : lowerHistoryPathBinding path80 := by
  apply pathBinding_from_ids path80 src80 [] recs80 wids preIDs 1025 1194
    ⟨premise_size, witness_size⟩ SourceValues16.source80 rfl records80 rfl
  · intro r hr _
    simp only [recs80, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [preIDs, lowerHistoryPremise, Nat.reduceSub, Option.getD_some] using (congrArg (fun o : Option (List Nat) => (o.getD []).map lowerHistoryBound) premise328)
  · intro r hr _
    simp only [recs80, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl
    · simpa only [wids, path80] using WitnessLookup16.witness949_projection
  · exact check80
  · exact BatchCoverage15.coverage_sound path80 recs80
      records80 SourceValues16.length80 BatchCoverageAll16.coverage80
end BatchIdSolution50
theorem _root_.solution : lowerHistoryBindingBatch 75 80 := by
  intro i hlo hhi p hp
  interval_cases i
  · have he := Option.some.inj (PathLookup16.path76_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path76_binding
  · have he := Option.some.inj (PathLookup16.path77_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path77_binding
  · have he := Option.some.inj (PathLookup16.path78_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path78_binding
  · have he := Option.some.inj (PathLookup16.path79_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path79_binding
  · have he := Option.some.inj (PathLookup16.path80_lookup.symm.trans hp)
    subst p
    exact BatchIdSolution50.path80_binding
end M7Binding50Sep15
#print axioms solution
