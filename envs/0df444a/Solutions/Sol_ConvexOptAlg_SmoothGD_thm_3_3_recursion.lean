-- Prove2me | solution 1 for ConvexOptAlg.SmoothGD.thm_3_3_recursion
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:47:46.736987+00:00
-- url     : https://prove2.me/submissions/e74a46db-9d8e-49f5-8bfc-b748e2f8a456

import Theorems.Thm_ConvexOptAlg_SmoothGD_thm_3_3_dist_decrease
import Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_4
import Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_5

open scoped InnerProductSpace
open ConvexOptAlg.SmoothGD

theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsGDRun g (1 / β) x) (s : ℕ) (hs : 1 ≤ s) :
    (f (x s) - f xstar) ^ 2 ≤
      2 * β * ‖x 1 - xstar‖ ^ 2 * ((f (x s) - f xstar) - (f (x (s + 1)) - f xstar)) := by
  have hdist : ∀ k : ℕ, 1 ≤ k → ‖x k - xstar‖ ≤ ‖x 1 - xstar‖ := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
        exact (thm_3_3_dist_decrease f g β hβ hconv hf xstar hmin x hrun k hk).2.trans ih
  have hgap : f (x s) - f xstar ≤ ⟪g (x s), x s - xstar⟫_ℝ := by
    have hh := (eq_3_4 f g β hconv hf xstar (x s)).1
    rw [show xstar - x s = -(x s - xstar) by abel, inner_neg_right] at hh
    linarith
  have hgn : f (x s) - f xstar ≤ ‖g (x s)‖ * ‖x 1 - xstar‖ :=
    hgap.trans ((real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hdist s hs) (norm_nonneg _)))
  have hsq : (f (x s) - f xstar) ^ 2 ≤ ‖g (x s)‖ ^ 2 * ‖x 1 - xstar‖ ^ 2 := by
    have hh := mul_self_le_mul_self (sub_nonneg.mpr (hmin (x s))) hgn
    nlinarith only [hh]
  have hd := eq_3_5 f g β hβ hconv hf (x s)
  rw [← hrun.2 s hs] at hd
  have hdes : ‖g (x s)‖ ^ 2 ≤ 2 * β * (f (x s) - f (x (s + 1))) := by
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * β by positivity)
    have he : 2 * β * (-(1 / (2 * β)) * ‖g (x s)‖ ^ 2) = -‖g (x s)‖ ^ 2 := by
      field_simp
    rw [he] at hh
    linarith
  calc
    (f (x s) - f xstar) ^ 2 ≤ ‖g (x s)‖ ^ 2 * ‖x 1 - xstar‖ ^ 2 := hsq
    _ ≤ (2 * β * (f (x s) - f (x (s + 1)))) * ‖x 1 - xstar‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hdes (sq_nonneg _)
    _ = _ := by ring
