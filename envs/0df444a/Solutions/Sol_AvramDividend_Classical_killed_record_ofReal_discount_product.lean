-- Prove2me | solution 1 for AvramDividend.Classical.killed_record_ofReal_discount_product
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T00:35:04.642387+00:00
-- url     : https://prove2.me/submissions/20635b17-01bf-4176-b1db-49cb4af2fcea

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential

open scoped ENNReal
theorem solution
    (ε q t : ℝ) (hε : 0 ≤ ε) :
    ENNReal.ofReal (ε * Real.exp (-(q * t))) =
      ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * t))) := by 
  exact ENNReal.ofReal_mul hε
