-- Prove2me | solution 2 for AvramDividend.Classical.killed_record_ofReal_discount_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:35:18.700502+00:00
-- url     : https://prove2.me/submissions/e921ba84-3b17-4a8a-b19e-e783cc126472

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

theorem solution
    (ε q t : ℝ) (hε : 0 ≤ ε) :
    ENNReal.ofReal (ε * Real.exp (-(q * t))) =
      ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * t))) := by
  rw [ENNReal.ofReal_mul hε]
