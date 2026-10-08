-- Prove2me | solution 1 for ConvexOptAlg.SmoothGD.eq_3_5
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:41:45.236988+00:00
-- url     : https://prove2.me/submissions/0f23356f-6a24-484f-b2fe-b90a9d611749

import Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_4

open scoped InnerProductSpace
open ConvexOptAlg.SmoothGD

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (x : EuclideanSpace ℝ (Fin n)) :
    f (x - (1 / β) • g x) - f x ≤ -(1 / (2 * β)) * ‖g x‖ ^ 2 := by
  have h := (eq_3_4 f g β hconv hf (x - (1 / β) • g x) x).2
  have he : x - (1 / β) • g x - x = -((1 / β) • g x) := by abel
  rw [he, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hβ)] at h
  have hc : β / 2 * (1 / β * ‖g x‖) ^ 2 = 1 / (2 * β) * ‖g x‖ ^ 2 := by
    field_simp
    <;> ring
  have hc' : 1 / β * ‖g x‖ ^ 2 = 2 * (1 / (2 * β) * ‖g x‖ ^ 2) := by ring
  rw [hc, hc'] at h
  linarith
