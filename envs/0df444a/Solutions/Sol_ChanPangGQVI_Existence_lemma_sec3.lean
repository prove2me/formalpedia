-- Prove2me | solution 1 for ChanPangGQVI.Existence.lemma_sec3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:40:27.927366+00:00
-- url     : https://prove2.me/submissions/e36d43e5-b7de-48e5-b0df-a8f983f84289

import Mathlib

open scoped RealInnerProductSpace

theorem solution {n : ℕ} (W Es : Set (EuclideanSpace ℝ (Fin n)))
    (hW : Convex ℝ W) (hEs : Convex ℝ Es) (hEs_solid : (interior Es).Nonempty)
    (x0 ystar : EuclideanSpace ℝ (Fin n)) (hx0 : x0 ∈ W ∩ interior Es)
    (h : ∀ x' ∈ W ∩ Es, 0 ≤ ⟪x' - x0, ystar⟫) :
    ∀ x' ∈ W, 0 ≤ ⟪x' - x0, ystar⟫ := by
  intro x hx
  obtain ⟨hx0W, hx0E⟩ := hx0
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x0 hx0E
  obtain ⟨t, ht0, ht1, htd⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t * ‖x - x0‖ < δ := by
    rcases eq_or_lt_of_le (norm_nonneg (x - x0)) with hn | hn
    · exact ⟨1, one_pos, le_rfl, by rw [← hn]; simpa using hδ⟩
    · refine ⟨min 1 (δ / (2 * ‖x - x0‖)), lt_min one_pos (by positivity),
        min_le_left _ _, ?_⟩
      have hm : min 1 (δ / (2 * ‖x - x0‖)) ≤ δ / (2 * ‖x - x0‖) := min_le_right _ _
      calc min 1 (δ / (2 * ‖x - x0‖)) * ‖x - x0‖
          ≤ (δ / (2 * ‖x - x0‖)) * ‖x - x0‖ := by gcongr
        _ = δ / 2 := by field_simp
        _ < δ := by linarith
  have hzW : x0 + t • (x - x0) ∈ W := by
    have hc := hW hx0W hx (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    have hEq : x0 + t • (x - x0) = (1 - t) • x0 + t • x := by module
    rw [hEq]; exact hc
  have hzE : x0 + t • (x - x0) ∈ Es := by
    refine interior_subset (hball ?_)
    simp only [Metric.mem_ball, dist_eq_norm]
    calc ‖x0 + t • (x - x0) - x0‖ = t * ‖x - x0‖ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      _ < δ := htd
  have hmain := h _ ⟨hzW, hzE⟩
  rw [add_sub_cancel_left, real_inner_smul_left] at hmain
  nlinarith [hmain, ht0]
