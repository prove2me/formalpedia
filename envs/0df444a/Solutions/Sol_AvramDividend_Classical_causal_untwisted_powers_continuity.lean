-- Prove2me | solution 1 for AvramDividend.Classical.causal_untwisted_powers_continuity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:49:33.976828+00:00
-- url     : https://prove2.me/submissions/8fbe21d1-8bdc-47b7-b8a3-85509a089678

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Complex.Exponential
open AvramDividend.Classical
theorem solution
    (F U : ℕ → ℝ → ℝ) (θ : ℝ)
    (hFcont : ∀ n : ℕ, Continuous (F n))
    (hrel : ∀ n : ℕ, ∀ x : ℝ,
      F n x = Real.exp (-(θ * x)) * U n x) :
    ∀ n : ℕ, Continuous (U n) := by 
  intro n
  have e : U n = fun x => Real.exp (θ * x) * F n x := by
    ext x
    rw [hrel n x, ← mul_assoc, ← Real.exp_add]
    simp
  rw [e]
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul (hFcont n)
