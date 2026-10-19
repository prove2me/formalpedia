-- Prove2me | solution 1 for Ehrhart.TorusCompactTestGreen.tsupport_normalizedCoverMollification_subset_cthickening
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/9b4701dd-d3cd-437a-9f3a-fdbb639e10d9

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusMollificationLocalL2Bounds_complexShrinkingBump_rOut_le_one

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusCompactTestGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open TorusMollificationLocalL2Bounds
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusCompactTestGreen
theorem _root_.solution
    {n : ℕ} {g : LogSpace n → ℂ}
    (k : ℕ) :
    tsupport (normalizedCoverMollification g k) ⊆
      Metric.cthickening 1 (tsupport g) := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  have hs := MeasureTheory.support_convolution_subset_swap
    (ContinuousLinearMap.lsmul ℝ ℝ) hx
  obtain ⟨u, hu, v, hv, huv⟩ := hs
  have hvball : v ∈ Metric.ball (0 : LogSpace n)
      (complexShrinkingBump (n := n) k).rOut := by
    rw [← (complexShrinkingBump (n := n) k).support_normed_eq
      (μ := (volume : Measure (LogSpace n)))]
    exact hv
  have hvnorm : ‖v‖ ≤ 1 := by
    have hvlt : ‖v‖ < (complexShrinkingBump (n := n) k).rOut := by
      simpa [Metric.mem_ball, dist_zero_right] using hvball
    exact hvlt.le.trans (complexShrinkingBump_rOut_le_one k)
  subst x
  apply Metric.mem_cthickening_of_dist_le
    (u + v) u 1 (tsupport g) (subset_closure hu)
  simpa [dist_eq_norm] using hvnorm
end Ehrhart.TorusCompactTestGreen
