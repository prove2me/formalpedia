-- Prove2me | solution 1 for Ehrhart.TorusStrongCoverMollificationDensity.normalizedCoverMollification_indicator_cthickening_eq_on
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/2943db78-d062-4825-a72f-5c6478482275

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
open Ehrhart.TorusStrongCoverMollificationDensity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity MatrixTorusBochnerCoreApproximation
open TorusWeakDolbeaultMollification TorusMollificationLocalL2Bounds TorusStrongCoverMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongCoverMollificationDensity
theorem _root_.solution
    {n : ℕ} {h : LogSpace n → ℂ}
    {K : Set (LogSpace n)} (_ : IsCompact K)
    (k : ℕ) (x : LogSpace n) (hx : x ∈ K) :
    normalizedCoverMollification h k x =
      normalizedCoverMollification
        ((Metric.cthickening 1 K).indicator h) k x := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  unfold normalizedCoverMollification
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : κ y = 0
  · simp [κ, hy]
  · have hball :
        y ∈ Metric.ball (0 : LogSpace n)
          (complexShrinkingBump (n := n) k).rOut := by
        rw [← (complexShrinkingBump (n := n) k).support_normed_eq
          (μ := (volume : Measure (LogSpace n)))]
        exact hy
    have hnorm :
        ‖y‖ < (complexShrinkingBump (n := n) k).rOut := by
      simpa [Metric.mem_ball, dist_zero_right] using hball
    have hxy : x - y ∈ Metric.cthickening 1 K := by
      apply Metric.mem_cthickening_of_dist_le
        (x - y) x 1 K hx
      rw [dist_eq_norm]
      have heq : (x - y) - x = -y := by abel
      rw [heq, norm_neg]
      exact hnorm.le.trans (complexShrinkingBump_rOut_le_one k)
    simp [Set.indicator_of_mem hxy]
end Ehrhart.TorusStrongCoverMollificationDensity
