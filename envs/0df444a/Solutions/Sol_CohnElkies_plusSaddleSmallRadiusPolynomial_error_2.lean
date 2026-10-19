-- Prove2me | solution 2 for CohnElkies.plusSaddleSmallRadiusPolynomial_error
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:25:45.264976+00:00
-- url     : https://prove2.me/submissions/e4f846e8-bb92-4f89-ac50-00f801760104

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology


theorem solution
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (n : ℕ) (hn : 2 * (n : ℝ) ≤ ℓ) :
    |((beta ε - (2 * (n : ℝ) / ℓ) *
          (2 + 2 * (n : ℝ) / ℓ) ^ 2) /
        beta ε) - 1| ≤
      (18 / beta ε) * ((n : ℝ) / ℓ) := by
  have hβ : 0 < beta ε := beta_pos hε
  have hx0 : 0 ≤ (n : ℝ) / ℓ := by positivity
  have hx1 : (n : ℝ) / ℓ ≤ 1 / 2 := by rw [div_le_iff₀ hℓ]; linarith
  set x := (n : ℝ) / ℓ with hxdef
  have h2 : 2 * (n : ℝ) / ℓ = 2 * x := by rw [hxdef]; ring
  rw [h2]
  have e : (beta ε - 2 * x * (2 + 2 * x) ^ 2) / beta ε - 1 = -(2 * x * (2 + 2 * x) ^ 2 / beta ε) := by
    field_simp; ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hβ]
  have : (2 + 2 * x) ^ 2 ≤ 9 := by nlinarith
  nlinarith

