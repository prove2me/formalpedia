-- Prove2me | solution 1 for ClassicalComplexWPT.seqDivision_factorizations_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:29.879031+00:00
-- url     : https://prove2.me/submissions/0775da23-e4d1-468d-819e-913676d49858

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
import Theorems.Thm_ClassicalComplexWPT_seqDivisionQuotient_unique
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
    (f q₁ r₁ q₂ r₂ : L1Coeff ℕ)
    (hfac₁ : f = seqLowShift d q₁ + convolution q₁ p + r₁)
    (hr₁ : seqHighShift d r₁ = 0)
    (hfac₂ : f = seqLowShift d q₂ + convolution q₂ p + r₂)
    (hr₂ : seqHighShift d r₂ = 0) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  have hq₁ : q₁ = seqDivisionQuotient d p hp f :=
    seqDivisionQuotient_unique d p hp f q₁ r₁ hfac₁ hr₁
  have hq₂ : q₂ = seqDivisionQuotient d p hp f :=
    seqDivisionQuotient_unique d p hp f q₂ r₂ hfac₂ hr₂
  have hq : q₁ = q₂ := hq₁.trans hq₂.symm
  refine ⟨hq, ?_⟩
  have hfac₁' : f = seqLowShift d q₂ + convolution q₂ p + r₁ := by
    simpa only [hq] using hfac₁
  have hsum : (seqLowShift d q₂ + convolution q₂ p) + r₁ =
      (seqLowShift d q₂ + convolution q₂ p) + r₂ := by
    simpa only [add_assoc] using hfac₁'.symm.trans hfac₂
  exact add_left_cancel hsum
end ClassicalComplexWPT
