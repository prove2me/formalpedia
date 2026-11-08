-- Prove2me | solution 1 for DensityExtension.ceilApprox_ge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:19:55.929147+00:00
-- url     : https://prove2.me/submissions/ded77451-4260-400d-896c-e0ac9c367aad

import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- Rounding a nonnegative real upward and dividing by a positive denominator dominates it. -/
theorem solution (t : ℝ≥0) (m : ℕ) :
    t ≤ DensityExtension.ceilApprox t m :=
  NNReal.coe_le_coe.mp (by
    show (t : ℝ) ≤ _
    simp only [DensityExtension.ceilApprox]
    rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < ↑(m + 1))).mpr (Nat.le_ceil _))
