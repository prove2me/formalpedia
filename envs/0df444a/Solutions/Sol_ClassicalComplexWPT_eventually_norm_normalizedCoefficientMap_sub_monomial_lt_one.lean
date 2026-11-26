-- Prove2me | solution 1 for ClassicalComplexWPT.eventually_norm_normalizedCoefficientMap_sub_monomial_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:57.153796+00:00
-- url     : https://prove2.me/submissions/a7caa6e6-c33a-46db-b0c9-6d26813fdb1d

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_originWeightedCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_normalizedOriginCoeffs_apply
import Theorems.Thm_ClassicalComplexWPT_analyticAt_normalizedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply


attribute [local simp] ClassicalComplexWPT.originWeightedCoeffs_apply
attribute [local simp] ClassicalComplexWPT.normalizedOriginCoeffs_apply

set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {n d : ℕ}
    (C : Base n → OriginSeq) (denom : ℂ) (hC : AnalyticAt ℂ C 0)
    (hclose : ‖normalizedCoefficientMap C denom 0 - monomialSeq d‖ < (1 : ℝ) / 2) :
    ∀ᶠ z in 𝓝 (0 : Base n),
      ‖normalizedCoefficientMap C denom z - monomialSeq d‖ < 1 := by
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  have hmem : normalizedCoefficientMap C denom 0 ∈
      Metric.ball (monomialSeq d) 1 := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact hclose.trans hhalf
  have hopen : Metric.ball (monomialSeq d) 1 ∈
      𝓝 (normalizedCoefficientMap C denom 0) :=
    Metric.isOpen_ball.mem_nhds hmem
  filter_upwards [(analyticAt_normalizedCoefficientMap C denom hC).continuousAt.eventually hopen]
    with z hz
  simpa [Metric.mem_ball, dist_eq_norm] using hz
end ClassicalComplexWPT
