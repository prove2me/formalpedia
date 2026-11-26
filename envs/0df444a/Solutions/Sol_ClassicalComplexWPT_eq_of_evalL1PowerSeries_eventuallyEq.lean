-- Prove2me | solution 1 for ClassicalComplexWPT.eq_of_evalL1PowerSeries_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:15:29.036671+00:00
-- url     : https://prove2.me/submissions/c561f90b-ea3c-4619-83e2-2d25a38064a2

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
theorem _root_.solution (a b : L1Sequence)
    (h : (fun w ↦ evalL1PowerSeries a w) =ᶠ[nhds 0]
      (fun w ↦ evalL1PowerSeries b w)) : a = b := by
  let appA : (L1Sequence →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ a
  let appB : (L1Sequence →L[ℂ] ℂ) →L[ℂ] ℂ :=
    ContinuousLinearMap.apply ℂ ℂ b
  let pA : FormalMultilinearSeries ℂ ℂ ℂ :=
    appA.compFormalMultilinearSeries l1OperatorSeries
  let pB : FormalMultilinearSeries ℂ ℂ ℂ :=
    appB.compFormalMultilinearSeries l1OperatorSeries
  have hrad : (0 : ℝ≥0∞) < l1OperatorSeries.radius :=
    (by norm_num : (0 : ℝ≥0∞) < 1).trans_le one_le_radius_l1OperatorSeries
  have hA : HasFPowerSeriesAt (fun w ↦ evalL1PowerSeries a w) pA 0 := by
    have hball := appA.comp_hasFPowerSeriesOnBall
      (l1OperatorSeries.hasFPowerSeriesOnBall hrad)
    exact hball.hasFPowerSeriesAt.congr (by
      filter_upwards
      intro w
      rfl)
  have hB : HasFPowerSeriesAt (fun w ↦ evalL1PowerSeries b w) pB 0 := by
    have hball := appB.comp_hasFPowerSeriesOnBall
      (l1OperatorSeries.hasFPowerSeriesOnBall hrad)
    exact hball.hasFPowerSeriesAt.congr (by
      filter_upwards
      intro w
      rfl)
  have hp : pA = pB := hA.eq_formalMultilinearSeries_of_eventually hB h
  apply lp.ext
  funext k
  have hk := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p k (fun _ ↦ (1 : ℂ))) hp
  simpa [pA, pB, appA, appB, l1OperatorSeries, coefficientEval, lp.evalCLM,
    ContinuousLinearMap.compFormalMultilinearSeries_apply] using hk
end ClassicalComplexWPT
