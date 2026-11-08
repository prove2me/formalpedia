-- Prove2me | solution 1 for DensityExtension.ceilApprox_coe
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:28:40.637558+00:00
-- url     : https://prove2.me/submissions/a3e8e37b-e240-4600-891c-7e33dc595a35

import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Mathlib.Data.NNReal.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- The nonnegative real ceiling approximation has its expected real coercion. -/
theorem solution (t : ℝ≥0) (m : ℕ) :
    (DensityExtension.ceilApprox t m : ℝ) = ↑⌈(t : ℝ) * ↑(m + 1)⌉₊ / ↑(m + 1) := by
  show NNReal.toReal _ = _
  simp only [DensityExtension.ceilApprox]
  rw [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast]
