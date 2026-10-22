-- Prove2me | solution 1 for BirkhoffGlobalSection.first_critical_value_near_half
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T20:52:09.309977+00:00
-- url     : https://prove2.me/submissions/1937b1e5-cbcf-477f-8b5e-49de136779c1

import Theorems.Thm_BirkhoffGlobalSection_inner_lagrange_realizes_first_critical_value
import Theorems.Thm_BirkhoffGlobalSection_jacobi_critical_momentum

/-! The first critical value is the Jacobi energy of the inner Lagrange point `L`. At `L` the
momentum is `(q₂, -q₁) = (0, -x + μ)`, so with `x = q₁ + μ ∈ (0, 1)`
`H(L) = -(x - μ)²/2 - (1-μ)/x - μ/(1-x) ≤ -(1/2 - |μ - 1/2|)(1/x + 1/(1-x)) ≤ -2 + 4|μ - 1/2|`. -/

namespace BirkhoffGlobalSection.FirstCritical

open BirkhoffGlobalSection

theorem inv_sum_ge {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y = 1) : 4 ≤ 1 / x + 1 / y := by
  rw [div_add_div _ _ hx.ne' hy.ne', le_div_iff₀ (mul_pos hx hy)]
  nlinarith [sq_nonneg (x - y)]

theorem first_critical_le (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ < 1) :
    firstCriticalValue μ ≤ -2 + 4 * |μ - 1 / 2| := by
  obtain ⟨L, hL, hval⟩ := inner_lagrange_realizes_first_critical_value μ hμ0 hμ1
  obtain ⟨_, hcrit, hlo, hhi, h1⟩ := hL
  obtain ⟨h2, h3⟩ := jacobi_critical_momentum μ L hcrit
  rw [← hval]
  set x := L 0 + μ with hx
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < 1 - x := by linarith
  have hr1 : Real.sqrt ((L 0 + μ) ^ 2 + L 1 ^ 2) = x := by
    rw [h1, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, ← hx, Real.sqrt_sq hx0.le]
  have hr2 : Real.sqrt ((L 0 - 1 + μ) ^ 2 + L 1 ^ 2) = 1 - x := by
    rw [h1, show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
      show (L 0 - 1 + μ) ^ 2 = (1 - x) ^ 2 by rw [hx]; ring, Real.sqrt_sq hy0.le]
  have hH : jacobiHamiltonian μ L = -(L 0) ^ 2 / 2 - (1 - μ) / x - μ / (1 - x) := by
    unfold jacobiHamiltonian
    rw [hr1, hr2, h2, h3, h1]
    ring
  rw [hH]
  have hinv := inv_sum_ge hx0 hy0 (by ring)
  have hd : |μ - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
  have hk : 0 ≤ 1 / 2 - |μ - 1 / 2| := by linarith
  have e1 : (1 / 2 - |μ - 1 / 2|) * (1 / x) ≤ (1 - μ) / x := by
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ hx0.le
    linarith [le_abs_self (μ - 1 / 2)]
  have e2 : (1 / 2 - |μ - 1 / 2|) * (1 / (1 - x)) ≤ μ / (1 - x) := by
    rw [mul_one_div]
    apply div_le_div_of_nonneg_right _ hy0.le
    linarith [neg_abs_le (μ - 1 / 2)]
  have e3 : (1 / 2 - |μ - 1 / 2|) * 4 ≤ (1 / 2 - |μ - 1 / 2|) * (1 / x + 1 / (1 - x)) :=
    mul_le_mul_of_nonneg_left hinv hk
  nlinarith [sq_nonneg (L 0)]

end BirkhoffGlobalSection.FirstCritical

open BirkhoffGlobalSection BirkhoffGlobalSection.FirstCritical in
theorem solution (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ μ : ℝ, 0 < μ → μ < 1 → |μ - 1 / 2| < ε →
      firstCriticalValue μ < -2 + η := by
  refine ⟨η / 8, by positivity, fun μ h0 h1 hμ => ?_⟩
  have := first_critical_le μ h0 h1
  linarith
