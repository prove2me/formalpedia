-- Prove2me | solution 1 for ClassicalComplexWPT.preparedTailSeq_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:14:31.231933+00:00
-- url     : https://prove2.me/submissions/bdd5602d-a5ac-47fa-9186-f8cc2a867e9b

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Theorems.Thm_ClassicalComplexWPT_preparedTailSeq_apply_fin
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionPerturbationMap_apply
import Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainder
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_divisionRemainderGlobal
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply
attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionOperatorInput_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionPerturbationMap_apply
attribute [local simp] ClassicalComplexWPT.seqDivisionRhsInput_apply
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainder
attribute [local simp] ClassicalComplexWPT.seqHighShift_divisionRemainderGlobal
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.preparedTailSeq_apply_fin

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} {r : ℝ≥0} (hr : 0 < r)
    (a a' : Fin d → Base n → ℂ) (z : Base n) :
    preparedTailSeq r d a z = preparedTailSeq r d a' z ↔
      ∀ i, a i z = a' i z := by
  constructor
  · intro h i
    have hi := congrArg (fun q : L1Sequence ↦ q (i : ℕ)) h
    rw [preparedTailSeq_apply_fin, preparedTailSeq_apply_fin] at hi
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hc : (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) ≠ 0 :=
      mul_ne_zero (inv_ne_zero (pow_ne_zero _ hrC)) (pow_ne_zero _ hrC)
    exact mul_left_cancel₀ hc hi
  · intro h
    unfold preparedTailSeq
    apply Finset.sum_congr rfl
    intro i hi
    rw [h i]
end ClassicalComplexWPT
