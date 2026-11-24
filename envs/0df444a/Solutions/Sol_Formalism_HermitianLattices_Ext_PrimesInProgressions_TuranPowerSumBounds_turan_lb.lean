-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds.turan_lb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:53.606213+00:00
-- url     : https://prove2.me/submissions/f0da2302-5f16-4b0d-a8e8-e985f6aa8142

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
theorem _root_.solution (C : ℝ) (hC : 0 < C) (a n m : ℕ) (hn : 1 ≤ n) :
    Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1)) ≤ ((n : ℝ) / (C * ((m : ℝ) + n))) ^ (a * n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hCm : 0 < max C 1 := lt_max_of_lt_right one_pos
  have h1 : Real.exp (-(m : ℝ) / n) * (m + n) ≤ n :=
    calc Real.exp (-(m : ℝ) / n) * (m + n) = n * (Real.exp (-(m : ℝ) / n) * ((m : ℝ) / n + 1)) := by
          field_simp
      _ ≤ n * (Real.exp (-(m : ℝ) / n) * Real.exp ((m : ℝ) / n)) := by
          gcongr
          exact Real.add_one_le_exp _
      _ = n := by
          rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, mul_one]
  have hb : Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ≤ (n : ℝ) / (C * (m + n)) := by
    rw [Real.exp_sub, Real.exp_log hCm]
    have h2 : Real.exp (-(m : ℝ) / n) ≤ n / (m + n) := by
      rw [le_div_iff₀ (by positivity)]
      exact h1
    calc Real.exp (-(m : ℝ) / n) / max C 1 ≤ ((n : ℝ) / (m + n)) / max C 1 := by gcongr
      _ ≤ ((n : ℝ) / (m + n)) / C := by
          gcongr
          exact le_max_left _ _
      _ = n / (C * (m + n)) := by rw [div_div, mul_comm]
  calc Real.exp (-((a : ℝ) * m) - a * n * Real.log (max C 1))
      = Real.exp (-(m : ℝ) / n - Real.log (max C 1)) ^ (a * n) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp
    _ ≤ ((n : ℝ) / (C * (m + n))) ^ (a * n) := pow_le_pow_left₀ (Real.exp_pos _).le hb _
end Formalism.HermitianLattices.Ext.PrimesInProgressions.TuranPowerSumBounds
