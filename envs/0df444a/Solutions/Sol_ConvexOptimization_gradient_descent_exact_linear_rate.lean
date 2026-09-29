-- Prove2me | solution 1 for ConvexOptimization.gradient_descent_exact_linear_rate
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T03:24:27.467653+00:00
-- url     : https://prove2.me/submissions/2c324f2c-f617-4514-ac92-62e85ad1114d

import Mathlib
import Theorems.Thm_ConvexOptimization_strong_convexity_quadratic_lower_bound

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n : ℕ} (m M : ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hsc : ∀ x y : EuclideanSpace ℝ (Fin n),
      f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (hsm : ∀ x y : EuclideanSpace ℝ (Fin n),
      f y ≤ f x + ⟪g x, y - x⟫ + M / 2 * ‖y - x‖ ^ 2)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinOn f Set.univ xstar)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hstep : ∀ k, (∃ t : ℝ, 0 ≤ t ∧ x (k + 1) = x k - t • g (x k)) ∧
      ∀ s : ℝ, 0 ≤ s → f (x (k + 1)) ≤ f (x k - s • g (x k))) :
    ∀ k, f (x k) - f xstar ≤ (1 - m / M) ^ k * (f (x 0) - f xstar) := by
  have hM : (0 : ℝ) < M := lt_of_lt_of_le hm hmM
  have hMne : M ≠ 0 := ne_of_gt hM
  have hrate : (0 : ℝ) ≤ 1 - m / M := by
    have : m / M ≤ 1 := (div_le_one hM).mpr hmM
    linarith
  -- Suboptimality controlled by the gradient norm (Eq. (9.9), the previous milestone).
  have hsub : ∀ z : EuclideanSpace ℝ (Fin n), f z - f xstar ≤ ‖g z‖ ^ 2 / (2 * m) :=
    fun z => ConvexOptimization.strong_convexity_quadratic_lower_bound m hm f g hg hsc xstar hstar z
  -- One step of exact line search contracts the suboptimality by the factor `1 − m/M`.
  have key : ∀ k, f (x (k + 1)) - f xstar ≤ (1 - m / M) * (f (x k) - f xstar) := by
    intro k
    set gk : EuclideanSpace ℝ (Fin n) := g (x k) with hgk
    -- (a) The step `s = 1/M` is available to the exact line search, and quadratic
    --     smoothness makes it decrease `f` by at least `‖gk‖²/(2M)`.
    have h1 := (hstep k).2 (1 / M) (by positivity)
    have h2 := hsm (x k) (x k - (1 / M) • gk)
    rw [show (x k - (1 / M) • gk) - x k = -((1 / M) • gk) from by abel] at h2
    rw [inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
      norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / M by positivity),
      mul_pow] at h2
    have hexp : f (x k) + -(1 / M * ‖gk‖ ^ 2) + M / 2 * ((1 / M) ^ 2 * ‖gk‖ ^ 2)
        = f (x k) - ‖gk‖ ^ 2 / (2 * M) := by
      field_simp
      ring
    rw [hexp] at h2
    have hD : ‖gk‖ ^ 2 / (2 * M) ≤ f (x k) - f (x (k + 1)) := by linarith
    -- (b) The gradient is large whenever the suboptimality is: `A ≤ ‖gk‖²/(2m)`.
    have hchain : m / M * (f (x k) - f xstar) ≤ m / M * (‖gk‖ ^ 2 / (2 * m)) :=
      mul_le_mul_of_nonneg_left (hsub (x k)) (div_nonneg hm.le hM.le)
    have heq : m / M * (‖gk‖ ^ 2 / (2 * m)) = ‖gk‖ ^ 2 / (2 * M) := by
      field_simp
    rw [heq] at hchain
    have hgoal : (1 - m / M) * (f (x k) - f xstar)
        = (f (x k) - f xstar) - m / M * (f (x k) - f xstar) := by ring
    rw [hgoal]
    linarith
  -- Iterate the contraction.
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc f (x (k + 1)) - f xstar
        ≤ (1 - m / M) * (f (x k) - f xstar) := key k
      _ ≤ (1 - m / M) * ((1 - m / M) ^ k * (f (x 0) - f xstar)) :=
          mul_le_mul_of_nonneg_left ih hrate
      _ = (1 - m / M) ^ (k + 1) * (f (x 0) - f xstar) := by ring
