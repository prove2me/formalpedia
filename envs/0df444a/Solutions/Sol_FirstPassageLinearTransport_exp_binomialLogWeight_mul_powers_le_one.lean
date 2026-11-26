-- Prove2me | solution 1 for FirstPassageLinearTransport.exp_binomialLogWeight_mul_powers_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:54:24.071923+00:00
-- url     : https://prove2.me/submissions/e9c532bb-302c-4aa5-bccc-5557ec0bbd2b

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Theorems.Thm_FirstPassageLinearTransport_binomial_log_mass_le_zero

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    Real.exp (binomialLogWeight n k) * p ^ k * (1 - p) ^ (n - k) ≤ 1 := by
  have hpComp : 0 < 1 - p := sub_pos.mpr hp₁
  have hlog := binomial_log_mass_le_zero hp₀ hp₁ hk hkn
  have hpPow : p ^ k = Real.exp ((k : ℝ) * Real.log p) := by
    rw [Real.exp_nat_mul, Real.exp_log hp₀]
  have hpCompPow :
      (1 - p) ^ (n - k) =
        Real.exp (((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
    rw [Real.exp_nat_mul, Real.exp_log hpComp]
  calc
    Real.exp (binomialLogWeight n k) * p ^ k * (1 - p) ^ (n - k) =
        Real.exp (binomialLogWeight n k + (k : ℝ) * Real.log p +
          ((n - k : ℕ) : ℝ) * Real.log (1 - p)) := by
      rw [hpPow, hpCompPow, Real.exp_add, Real.exp_add]
    _ ≤ Real.exp 0 := Real.exp_le_exp.mpr hlog
    _ = 1 := Real.exp_zero
end FirstPassageLinearTransport
