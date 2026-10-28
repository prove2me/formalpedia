-- Prove2me | solution 1 for AvramDividend.Classical.first_jump_discount_survival_kernel_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T19:09:33.641877+00:00
-- url     : https://prove2.me/submissions/7806239b-4216-4e49-b033-468c0fbb2762

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

theorem solution (d q rate t : ℝ) :
    ENNReal.ofReal (Real.exp (-(rate * t))) *
      ENNReal.ofReal (d * Real.exp (-(q * t))) =
    ENNReal.ofReal (d * Real.exp (-((q + rate) * t))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  congr 1
  calc
    Real.exp (-(rate * t)) * (d * Real.exp (-(q * t))) =
      d * (Real.exp (-(rate * t)) * Real.exp (-(q * t))) := by ring
    _ = d * Real.exp (-(rate * t) + -(q * t)) := by rw [Real.exp_add]
    _ = d * Real.exp (-((q + rate) * t)) := by congr 1; ring
