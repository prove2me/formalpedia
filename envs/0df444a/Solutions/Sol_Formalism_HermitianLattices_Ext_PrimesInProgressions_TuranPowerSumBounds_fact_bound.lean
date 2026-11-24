-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.fact_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:52.41689+00:00
-- url     : https://prove2.me/submissions/d7810738-fae9-49fa-ad8b-797893746a1d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsPowerSumLowerBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x) (j : ℕ) (hj : 1 ≤ j) :
    x ^ j / ((j - 1).factorial : ℝ) ≤ j * (Real.exp 1 * x / j) ^ j := by
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj
  have hF : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hF1 : ((j - 1).factorial : ℝ) ≠ 0 := by positivity
  have hP : (0 : ℝ) < (j : ℝ) ^ j := pow_pos hjpos j
  have hfact : ((j - 1).factorial : ℝ) * j = j.factorial := by
    have : j * (j - 1).factorial = j.factorial := by
      first
        | exact Nat.mul_factorial_pred (show j ≠ 0 by omega)
        | exact Nat.mul_factorial_pred (show 0 < j by omega)
    rw [← this]
    push_cast
    ring
  have hkey : (j : ℝ) ^ j / j.factorial ≤ Real.exp 1 ^ j :=
    calc (j : ℝ) ^ j / j.factorial ≤ Real.exp j := by
          first
            | exact Real.pow_div_factorial_le_exp _ hjpos.le j
            | exact Real.pow_div_factorial_le_exp hjpos.le j
      _ = Real.exp 1 ^ j := by rw [← Real.exp_nat_mul, mul_one]
  have h1 : 1 / (j.factorial : ℝ) ≤ Real.exp 1 ^ j / (j : ℝ) ^ j := by
    rw [div_le_div_iff₀ hF hP]
    rw [div_le_iff₀ hF] at hkey
    linarith
  have hx' : 0 ≤ (j : ℝ) * x ^ j := by positivity
  calc x ^ j / ((j - 1).factorial : ℝ) = ((j : ℝ) * x ^ j) * (1 / j.factorial) := by
        rw [← hfact]
        field_simp
    _ ≤ ((j : ℝ) * x ^ j) * (Real.exp 1 ^ j / (j : ℝ) ^ j) := mul_le_mul_of_nonneg_left h1 hx'
    _ = j * (Real.exp 1 * x / j) ^ j := by
        rw [div_pow, mul_pow]
        ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
