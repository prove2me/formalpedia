-- Prove2me | solution 1 for ConsistentSubmodular.LowRollback.remainder_positive
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:40.786195+00:00
-- url     : https://prove2.me/submissions/a3060590-b02b-4ed3-a442-220d39228758

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackAfter

section

set_option maxHeartbeats 2000000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem solution (x q : ℝ) (hx0 : -(1 / 2) ≤ x) (hx1 : x ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 < remainder x q := by
  let A₄ := -(3 - q) * (2 - q) ^ 2
  let A₃ := 3 * (q - 2) ^ 2
  let A₂ := (2 - q) * (5 * q ^ 2 - 25 * q + 54)
  let A₁ := -3 * (q ^ 3 - 3 * q ^ 2 - 4 * q + 4)
  let A₀ := -2 * q ^ 3 + 14 * q ^ 2 - 20 * q + 12
  have hq2 : (2 - q) ^ 2 ≤ 4 := by nlinarith
  have hA₄ : -12 ≤ A₄ := by
    have hm := mul_le_mul (show 3 - q ≤ 3 by linarith) hq2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    dsimp [A₄]
    linarith
  have hA₃ : 0 ≤ A₃ ∧ A₃ ≤ 12 := by dsimp [A₃]; constructor; positivity; nlinarith
  have hA₂ : 34 ≤ A₂ := by
    have hm := mul_nonneg (show 0 ≤ 1 - q by linarith)
      (show 0 ≤ 5 * q ^ 2 - 30 * q + 74 by nlinarith [sq_nonneg q])
    dsimp [A₂]
    nlinarith
  have hA₁ : -12 ≤ A₁ ∧ A₁ ≤ 6 := by
    have hm1 := mul_nonneg (show 0 ≤ 3 * q by positivity)
      (show 0 ≤ 4 + 3 * q - q ^ 2 by nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)])
    have hm2 := mul_nonneg (show 0 ≤ 3 * (1 - q) by linarith)
      (show 0 ≤ -q ^ 2 + 2 * q + 6 by nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)])
    dsimp [A₁]
    constructor <;> nlinarith
  have hA₀ : 20 / 7 ≤ A₀ := by
    have hq3 : q ^ 3 ≤ 1 := by exact pow_le_one₀ hq0 hq1
    dsimp [A₀]
    nlinarith [sq_nonneg (q - 5 / 7)]
  have hx2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have hx4 : x ^ 4 ≤ x ^ 2 / 4 := by
    have hm := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2)
    nlinarith
  have hquartic : -3 * x ^ 2 ≤ A₄ * x ^ 4 := by
    have hm := mul_nonneg (show 0 ≤ A₄ + 12 by linarith) (pow_nonneg (sq_nonneg x) 2)
    nlinarith
  have hquadratic : 34 * x ^ 2 ≤ A₂ * x ^ 2 := mul_le_mul_of_nonneg_right hA₂ (sq_nonneg x)
  have hid : remainder x q = A₄ * x ^ 4 + A₃ * x ^ 3 + A₂ * x ^ 2 + A₁ * x + A₀ := by dsimp [remainder, A₄, A₃, A₂, A₁, A₀]; ring
  rw [hid]
  by_cases hx : 0 ≤ x
  · have hcubic := mul_nonneg hA₃.1 (pow_nonneg hx 3)
    have hlinear : -12 * x ≤ A₁ * x := mul_le_mul_of_nonneg_right hA₁.1 hx
    nlinarith only [hquartic, hquadratic, hcubic, hlinear, hA₀, sq_nonneg (x - 6 / 31)]
  · have hxneg : x ≤ 0 := le_of_not_ge hx
    have hx3 : x ^ 3 ≤ 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hxneg]
    have hclow : -6 * x ^ 2 ≤ A₃ * x ^ 3 := by
      have h1 := mul_le_mul_of_nonpos_right hA₃.2 hx3
      have h2 := mul_nonneg (sq_nonneg x) (show 0 ≤ x + 1 / 2 by linarith)
      nlinarith
    have hlinear : 6 * x ≤ A₁ * x := mul_le_mul_of_nonpos_right hA₁.2 hxneg
    nlinarith only [hquartic, hquadratic, hclow, hlinear, hA₀, sq_nonneg (x + 3 / 25)]

end
