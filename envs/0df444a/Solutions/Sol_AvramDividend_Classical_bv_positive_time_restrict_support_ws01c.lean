-- Prove2me | solution 1 for AvramDividend.Classical.bv_positive_time_restrict_support_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:27:44.979982+00:00
-- url     : https://prove2.me/submissions/b5abc282-b32b-4241-b7b9-4001676ed214

import Mathlib
open MeasureTheory Set Filter
theorem solution :
    ∀ᵐ t : ℝ ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      t ∈ Ioc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioc
