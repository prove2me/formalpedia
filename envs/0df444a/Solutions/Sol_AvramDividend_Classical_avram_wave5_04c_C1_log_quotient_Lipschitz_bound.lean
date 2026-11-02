-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_log_quotient_Lipschitz_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:23:47.15677+00:00
-- url     : https://prove2.me/submissions/e0f34bdc-1a74-4c16-9905-1608ba5d6884

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set

/-! The derivative-filled logarithmic chord quotient obeys an exact
Lipschitz bound after multiplication by the BV endpoint weight (1-t). -/
theorem solution
    (w : ℝ → ℝ) (L : ℝ)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    |(1 - t) *
      Function.update
        (fun s : ℝ => (w (x + Real.log s) - w x) / (s - 1))
        1 (deriv w x) t| ≤ L * |Real.log t| := by
  let f : ℝ → ℝ :=
    Function.update
      (fun s : ℝ => (w (x + Real.log s) - w x) / (s - 1))
      1 (deriv w x)
  have hcorrect : (1 - t) * f t = w x - w (x + Real.log t) := by
    by_cases h1 : t = 1
    · simp [h1]
    · have hfr : f t = (w (x + Real.log t) - w x) / (t - 1) := by
        simp [f, h1]
      rw [hfr]
      have hne : t - 1 ≠ 0 := sub_ne_zero.mpr h1
      field_simp
      ring
  change |(1 - t) * f t| ≤ L * |Real.log t|
  rw [hcorrect]
  have h := hLip x (x + Real.log t)
  have hr : x - (x + Real.log t) = -(Real.log t) := by ring
  simpa [hr] using h
