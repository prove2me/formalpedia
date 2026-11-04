-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ubv_strict_C2_interior_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:00:21.606928+00:00
-- url     : https://prove2.me/submissions/f8235928-fb48-46bc-b06f-e905ab03cb09

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original strict below-cap C² domain is open, including σ = 0. -/
theorem solution (C : ℝ≥0∞) :
    IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
  change IsOpen
    (Ioi (0 : ℝ) ∩ (fun y : ℝ => ENNReal.ofReal y) ⁻¹' Iio C)
  exact isOpen_Ioi.inter
    (isOpen_Iio.preimage ENNReal.continuous_ofReal)
