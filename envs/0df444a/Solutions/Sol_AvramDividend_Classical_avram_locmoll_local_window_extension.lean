-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_local_window_extension
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:42:35.471142+00:00
-- url     : https://prove2.me/submissions/6147552b-b355-4930-9bbb-a6bfaeefcd41

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_locmoll_compact_cutoff
open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false
theorem solution
    (w V : ℝ → ℝ) (C : ℝ≥0∞) (δ y : ℝ)
    (hδ : 0 < δ) (hy : δ ≤ y) (hyC : ENNReal.ofReal y ≤ C)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hV : ∀ z : ℝ, ENNReal.ofReal z ≤ C → V z = w z) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ z ∈ Ioo (y - 5 * δ / 6) (y - δ / 6), F z = w z ∧ V z = w z) := by 
  let s : Set ℝ := {z | 0 < z ∧ ENNReal.ofReal z < C}
  have hs : IsOpen s :=
    isOpen_lt continuous_const continuous_id |>.inter
      (isOpen_lt ENNReal.continuous_ofReal continuous_const)
  have hR : Metric.closedBall (y - δ / 2) (5 * δ / 12) ⊆ s := by
    intro z hz
    have hh : |z - (y - δ / 2)| ≤ 5 * δ / 12 := by
      simpa only [Metric.mem_closedBall, Real.dist_eq] using hz
    obtain ⟨hl, hu⟩ := abs_le.mp hh
    have hzy : z < y := by linarith
    refine ⟨by linarith, lt_of_lt_of_le
      ((ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < y)).2 hzy) hyC⟩
  obtain ⟨F, hF, hFc, he⟩ := avram_locmoll_compact_cutoff w s hs hw
    (y - δ / 2) (δ / 3) (5 * δ / 12) (by linarith) (by linarith) hR
  refine ⟨F, hF, hFc, ?_⟩
  intro z hz
  have hb : z ∈ Metric.ball (y - δ / 2) (δ / 3) := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  exact ⟨he hb, hV z ((ENNReal.ofReal_le_ofReal (by linarith [hz.2] : z ≤ y)).trans hyC)⟩
