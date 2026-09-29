-- Prove2me | solution 1 for ConvexOptimization.strong_convexity_quadratic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T03:14:41.162803+00:00
-- url     : https://prove2.me/submissions/df23408f-532e-47bf-8c96-4004410f789c

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n : ℕ} (m : ℝ) (hm : 0 < m)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ x, HasGradientAt f (g x) x)
    (hsc : ∀ x y : EuclideanSpace ℝ (Fin n),
      f x + ⟪g x, y - x⟫ + m / 2 * ‖y - x‖ ^ 2 ≤ f y)
    (xstar : EuclideanSpace ℝ (Fin n)) (hstar : IsMinOn f Set.univ xstar)
    (x : EuclideanSpace ℝ (Fin n)) :
    f x - f xstar ≤ ‖g x‖ ^ 2 / (2 * m) := by
  -- Strong convexity evaluated at the minimiser: the quadratic lower bound at `x`
  -- must still sit below `f xstar`.
  have h := hsc x xstar
  set v : EuclideanSpace ℝ (Fin n) := xstar - x with hv
  -- Completing the square: `0 ≤ ‖m • v + g x‖² = m²‖v‖² + 2m⟪g x, v⟫ + ‖g x‖²`.
  have hsq : (0 : ℝ) ≤ ‖m • v + g x‖ ^ 2 := sq_nonneg _
  rw [norm_add_sq_real, norm_smul, real_inner_smul_left] at hsq
  have hnorm : ‖(m : ℝ)‖ = m := Real.norm_of_nonneg hm.le
  rw [hnorm, mul_pow] at hsq
  have hcomm : ⟪v, g x⟫ = ⟪g x, v⟫ := real_inner_comm _ _
  rw [hcomm] at hsq
  have h2m : (0 : ℝ) < 2 * m := by linarith
  rw [le_div_iff₀ h2m]
  have hstep : (f x - f xstar) * (2 * m) ≤ (-⟪g x, v⟫ - m / 2 * ‖v‖ ^ 2) * (2 * m) :=
    mul_le_mul_of_nonneg_right (by linarith) h2m.le
  nlinarith [hsq, hstep]
