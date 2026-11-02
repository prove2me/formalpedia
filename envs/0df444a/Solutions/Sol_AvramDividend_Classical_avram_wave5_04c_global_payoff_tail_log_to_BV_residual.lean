-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_global_payoff_tail_log_to_BV_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:45:29.566508+00:00
-- url     : https://prove2.me/submissions/fa3f8f28-f68e-4739-a664-74fba4697557

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set

/-! Sharp exponential compactification keeps the signed payoff tail,
which is Levy-integrable without a global negative jump first moment. -/
theorem solution (w : ℝ → ℝ) (Q : Polynomial ℝ)
    (x M ε : ℝ) (hM : 0 ≤ M)
    (hQ : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |Polynomial.eval (t : ℝ) Q -
        (w x - w (x + Real.log (t : ℝ)))| ≤
        ε * (1 - (t : ℝ)) +
          (if (t : ℝ) < Real.exp (-M)
            then 2 * |w x - w (x + Real.log (t : ℝ))| else 0)) :
    ∀ r : ℝ, 0 ≤ r →
      |Polynomial.eval (Real.exp (-r)) Q - (w x - w (x - r))| ≤
        ε * (1 - Real.exp (-r)) +
          (if M < r then 2 * |w x - w (x - r)| else 0) := by
  intro r hr
  have he0 : 0 < Real.exp (-r) := Real.exp_pos _
  have he1 : Real.exp (-r) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  let t : unitInterval.Elem := ⟨Real.exp (-r), ⟨he0.le, he1⟩⟩
  have ht : (t : ℝ) = Real.exp (-r) := rfl
  have hlog : Real.log (t : ℝ) = -r := by rw [ht, Real.log_exp]
  have hcut : ((t : ℝ) < Real.exp (-M)) ↔ M < r := by
    rw [ht, Real.exp_lt_exp]
    constructor <;> intro h <;> linarith
  have h := hQ t (by simpa only [ht] using he0)
  rw [hlog] at h
  simp only [hcut] at h
  simpa only [ht, sub_eq_add_neg] using h
