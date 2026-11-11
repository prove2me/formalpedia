-- Prove2me | solution 1 for CapacitatedKMedianFPT.Main.fact_1
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-10T21:26:25.860472+00:00
-- url     : https://prove2.me/submissions/53d4aa4a-b756-491e-bbe7-d9e2e0e51c38

import Mathlib

set_option autoImplicit false

/-- **Fact 1** (p. 6, proof p. 22–23). `(log m)^t ≤ m · t!` for all integers `t ≥ 0` and all real
`m ≥ 1` (natural logarithm). -/
theorem solution (t : ℕ) (m : ℝ) (hm : 1 ≤ m) :
    Real.log m ^ t ≤ m * (t.factorial : ℝ) := by
  have h0 : 0 ≤ Real.log m := Real.log_nonneg hm
  have := Real.pow_div_factorial_le_exp (Real.log m) h0 t
  rw [Real.exp_log (by linarith)] at this
  have hf : (0:ℝ) < t.factorial := by exact_mod_cast t.factorial_pos
  rw [div_le_iff₀ hf] at this
  linarith
