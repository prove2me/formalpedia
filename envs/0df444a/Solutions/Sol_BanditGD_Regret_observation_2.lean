-- Prove2me | solution 1 for BanditGD.Regret.observation_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T21:39:45.732983+00:00
-- url     : https://prove2.me/submissions/37eed6e8-0692-48aa-9b15-23178bf169a9

import Mathlib

open scoped Pointwise in
theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∀ x ∈ (1 - α) • S, Metric.closedBall x (α * r) ⊆ S := by
  intro x hx y hy
  obtain ⟨s, hs, rfl⟩ := hx
  dsimp only at hy ⊢
  rcases hα0.eq_or_lt with h0 | hpos
  · subst h0
    rw [zero_mul, Metric.closedBall_zero, Set.mem_singleton_iff] at hy
    rw [hy]
    simpa using hs
  · have hz : α⁻¹ • (y - (1 - α) • s) ∈ S := by
      apply hrS
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hpos]
      rw [Metric.mem_closedBall, dist_eq_norm] at hy
      rw [inv_mul_le_iff₀ hpos]
      exact hy
    have key : y = (1 - α) • s + α • (α⁻¹ • (y - (1 - α) • s)) := by
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
      abel
    rw [key]
    exact hSconv hs hz (by linarith) hα0 (by ring)
