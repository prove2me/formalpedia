-- Prove2me | solution 1 for ClassicalComplexWPT.preparedTailSeq_apply_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:24.193803+00:00
-- url     : https://prove2.me/submissions/7530dc2b-a13c-442e-aaf6-5046f7bfb764

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Theorems.Thm_ClassicalComplexWPT_constantOneSeq_apply
import Theorems.Thm_ClassicalComplexWPT_convolution_constantOneSeq
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


attribute [local simp] ClassicalComplexWPT.constantOneSeq_apply
attribute [local simp] ClassicalComplexWPT.convolution_constantOneSeq

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (z : Base n) (i : Fin d) :
    preparedTailSeq r d a z (i : ℕ) =
      (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) * a i z := by
  classical
  change (lp.evalCLM ℂ (fun _ : ℕ ↦ ℂ) 1 (i : ℕ))
    (∑ j : Fin d, (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (j : ℕ)) •
      lp.single 1 (j : ℕ) (a j z)) = _
  rw [map_sum, Finset.sum_eq_single i]
  · rw [map_smul]
    change (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) *
      ((lp.single 1 (i : ℕ) (a i z) : L1Sequence) (i : ℕ)) = _
    rw [lp.single_apply_self]
  · intro j hj hji
    have hval : (j : ℕ) ≠ (i : ℕ) := by
      exact fun h ↦ hji (Fin.ext h)
    rw [map_smul]
    change _ * ((lp.single 1 (j : ℕ) (a j z) : L1Sequence) (i : ℕ)) = 0
    have hs : ((lp.single 1 (j : ℕ) (a j z) : L1Sequence) (i : ℕ)) = 0 :=
      lp.single_apply_ne (E := fun _ : ℕ ↦ ℂ) 1 (j : ℕ) (a j z) hval.symm
    rw [hs, mul_zero]
  · simp
end ClassicalComplexWPT
