-- Prove2me | solution 1 for AvramDividend.Classical.exp_negative_compensated_secant_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T21:51:49.428501+00:00
-- url     : https://prove2.me/submissions/55400c51-c352-4b0a-9098-030f36d0260e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_exp_negative_secant_mono

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

theorem solution
    (y θ₁ θ₂ : ℝ) (hy : y < 0)
    (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ₂) :
    (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ ≤
      (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ := by
  have hθ₂ : 0 < θ₂ := lt_of_lt_of_le hθ₁ hθ
  have hsec := exp_negative_secant_mono y θ₁ θ₂ hy hθ₁ hθ
  have heq₁ :
      (Real.exp (θ₁ * y) - 1 - θ₁ * y) / θ₁ =
        (Real.exp (θ₁ * y) - 1) / θ₁ - y := by
    field_simp [ne_of_gt hθ₁] <;> ring
  have heq₂ :
      (Real.exp (θ₂ * y) - 1 - θ₂ * y) / θ₂ =
        (Real.exp (θ₂ * y) - 1) / θ₂ - y := by
    field_simp [ne_of_gt hθ₂] <;> ring
  rw [heq₁, heq₂]
  linarith
