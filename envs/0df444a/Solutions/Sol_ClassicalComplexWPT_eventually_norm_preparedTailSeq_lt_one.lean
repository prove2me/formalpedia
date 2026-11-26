-- Prove2me | solution 1 for ClassicalComplexWPT.eventually_norm_preparedTailSeq_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:16:00.982843+00:00
-- url     : https://prove2.me/submissions/7eb8b3bb-5ba8-48d3-9998-d4a72b999cb1

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
import Theorems.Thm_ClassicalComplexWPT_analyticAt_preparedTailSeq
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
    (a : Fin d → Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0) :
    ∀ᶠ z in nhds (0 : Base n), ‖preparedTailSeq r d a z‖ < 1 := by
  have hzero : preparedTailSeq r d a 0 = 0 := by
    classical
    unfold preparedTailSeq
    simp [ha0]
  have hcont := (analyticAt_preparedTailSeq r a ha).continuousAt
  have hopen : Metric.ball (0 : L1Sequence) 1 ∈
      nhds (preparedTailSeq r d a 0) := by
    rw [hzero]
    exact Metric.isOpen_ball.mem_nhds (by simp)
  filter_upwards [hcont.eventually hopen] with z hz
  simpa [Metric.mem_ball, dist_zero_right] using hz
end ClassicalComplexWPT
