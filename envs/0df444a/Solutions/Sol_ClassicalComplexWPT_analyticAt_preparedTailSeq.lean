-- Prove2me | solution 1 for ClassicalComplexWPT.analyticAt_preparedTailSeq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:11.714473+00:00
-- url     : https://prove2.me/submissions/7165b57e-e050-4472-b5dc-57cc019c0c02

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
import Theorems.Thm_ClassicalComplexWPT_preparedTailSeq_apply_fin
import Theorems.Thm_ClassicalComplexWPT_seqHighShift_preparedTailSeq
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
attribute [local simp] ClassicalComplexWPT.preparedTailSeq_apply_fin
attribute [local simp] ClassicalComplexWPT.seqHighShift_preparedTailSeq

set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    AnalyticAt ℂ (preparedTailSeq r d a) 0 := by
  classical
  have hsum : AnalyticAt ℂ
      (∑ i : Fin d, fun z ↦ (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) •
        (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 1 (i : ℕ)) (a i z)) 0 := by
    apply Finset.univ.analyticAt_sum
    intro i hi
    let single : ℂ →L[ℂ] L1Sequence :=
      lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 1 (i : ℕ)
    have hs : AnalyticAt ℂ (fun z ↦ single (a i z)) 0 :=
      (single.analyticAt (a i 0)).comp (f := a i) (ha i)
    have hscaled : AnalyticAt ℂ
        (((((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ))) •
          (fun z ↦ single (a i z))) 0 := hs.const_smul
    have heq : (((((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ))) •
          (fun z ↦ single (a i z))) =
        (fun z ↦ ((((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ))) • single (a i z)) := by
      rfl
    change AnalyticAt ℂ
      (fun z ↦ ((((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ))) • single (a i z)) 0
    rw [← heq]
    exact hscaled
  change AnalyticAt ℂ (fun z ↦ preparedTailSeq r d a z) 0
  have heq : (fun z ↦ preparedTailSeq r d a z) =
      ∑ i : Fin d, fun z ↦ (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) •
        (lp.singleContinuousLinearMap ℂ (fun _ : ℕ ↦ ℂ) 1 (i : ℕ)) (a i z) := by
    funext z
    simp only [preparedTailSeq, Finset.sum_apply,
      lp.singleContinuousLinearMap_apply]
  rw [heq]
  exact hsum
end ClassicalComplexWPT
