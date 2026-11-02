-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_global_Bernstein_log_to_BV_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:30:45.234334+00:00
-- url     : https://prove2.me/submissions/b6b40f50-772f-4faa-b6cf-6c41f3a0292a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set

/-! Exponential compactification translates the global weighted C1
polynomial error back to the true nonnegative BV residual size. -/
theorem solution (w : ℝ → ℝ) (Q : Polynomial ℝ)
    (x M ε L : ℝ) (hM : 0 ≤ M)
    (hQ : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |Polynomial.eval (t : ℝ) Q -
        (w x - w (x + Real.log (t : ℝ)))| ≤
        ε * (1 - (t : ℝ)) +
          (if (t : ℝ) < Real.exp (-M)
            then 2 * L * |Real.log (t : ℝ)| else 0)) :
    ∀ r : ℝ, 0 ≤ r →
      |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
        ε * (1 - Real.exp (-r)) +
          (if M < r then 2 * L * r else 0) := by
  intro r hr
  have he0 : 0 < Real.exp (-r) := Real.exp_pos _
  have he1 : Real.exp (-r) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  let t : unitInterval.Elem := ⟨Real.exp (-r), ⟨he0.le, he1⟩⟩
  have ht : (t : ℝ) = Real.exp (-r) := rfl
  have hlog : Real.log (t : ℝ) = -r := by
    rw [ht, Real.log_exp]
  have hcut : ((t : ℝ) < Real.exp (-M)) ↔ M < r := by
    rw [ht, Real.exp_lt_exp]
    constructor <;> intro h <;> linarith
  have habs : |Real.log (t : ℝ)| = r := by
    rw [hlog, abs_neg, abs_of_nonneg hr]
  have hx : x + Real.log (t : ℝ) = x - r := by rw [hlog]; ring
  have h := hQ t (by simpa only [ht] using he0)
  rw [hlog] at h
  simp only [hcut, abs_neg, abs_of_nonneg hr] at h
  simpa only [ht, sub_eq_add_neg] using h
