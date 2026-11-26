-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivision_zero_remainder_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:50.655691+00:00
-- url     : https://prove2.me/submissions/397a6753-900c-42bc-acbb-de1103e69cc2

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
import Theorems.Thm_ClassicalComplexWPT_seqDivision_factorizations_unique
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
theorem _root_.solution (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f q q' r : L1Coeff ℕ)
    (hfac : f = seqLowShift d q + convolution q p)
    (hfac' : f = seqLowShift d q' + convolution q' p + r)
    (hr : seqHighShift d r = 0) :
    q = q' ∧ r = 0 := by
  have hz : seqHighShift d (0 : L1Coeff ℕ) = 0 := by
    apply lp.ext
    funext k
    rfl
  have hfac₀ : f = seqLowShift d q + convolution q p + (0 : L1Coeff ℕ) := by
    simpa using hfac
  have h := seqDivision_factorizations_unique d p hp f q 0 q' r hfac₀ hz hfac' hr
  exact ⟨h.1, h.2.symm⟩
end ClassicalComplexWPT
