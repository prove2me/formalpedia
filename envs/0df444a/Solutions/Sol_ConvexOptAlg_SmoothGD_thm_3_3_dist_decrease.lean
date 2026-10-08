-- Prove2me | solution 1 for ConvexOptAlg.SmoothGD.thm_3_3_dist_decrease
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:45:37.030264+00:00
-- url     : https://prove2.me/submissions/41d3c1e2-489c-4d49-a52e-f852c8ab0876

import Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_5
import Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_6

open scoped InnerProductSpace
open ConvexOptAlg.SmoothGD

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsGDRun g (1 / β) x) (s : ℕ) (hs : 1 ≤ s) :
    ‖x (s + 1) - xstar‖ ^ 2 ≤ ‖x s - xstar‖ ^ 2 - 1 / β ^ 2 * ‖g (x s)‖ ^ 2 ∧
      ‖x (s + 1) - xstar‖ ≤ ‖x s - xstar‖ := by
  have hz : g xstar = 0 := by
    have hh := eq_3_5 f g β hβ hconv hf xstar
    have hmin' := hmin (xstar - (1 / β) • g xstar)
    have hcoef : 0 < 1 / (2 * β) := by positivity
    have hsq : ‖g xstar‖ ^ 2 ≤ 0 := by
      apply (mul_le_mul_iff_right₀ hcoef).mp
      linarith
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (g xstar)]
  have hc := eq_3_6 f g β hβ hconv hf (x s) xstar
  rw [hz, sub_zero] at hc
  have he : ‖x (s + 1) - xstar‖ ^ 2 = ‖x s - xstar‖ ^ 2 -
      2 / β * ⟪g (x s), x s - xstar⟫_ℝ + 1 / β ^ 2 * ‖g (x s)‖ ^ 2 := by
    rw [hrun.2 s hs, sub_right_comm, norm_sub_sq_real, real_inner_smul_right,
      real_inner_comm (x s - xstar) (g (x s)), norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr hβ)]
    ring
  have hmul := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 / β by positivity)
  have hsq : ‖x (s + 1) - xstar‖ ^ 2 ≤
      ‖x s - xstar‖ ^ 2 - 1 / β ^ 2 * ‖g (x s)‖ ^ 2 := by
    rw [he]
    have hcoef : 2 / β * (1 / β * ‖g (x s)‖ ^ 2) =
        2 * (1 / β ^ 2 * ‖g (x s)‖ ^ 2) := by ring
    rw [hcoef] at hmul
    linarith
  refine ⟨hsq, ?_⟩
  have hn : 0 ≤ 1 / β ^ 2 * ‖g (x s)‖ ^ 2 := by positivity
  nlinarith [norm_nonneg (x (s + 1) - xstar), norm_nonneg (x s - xstar)]
