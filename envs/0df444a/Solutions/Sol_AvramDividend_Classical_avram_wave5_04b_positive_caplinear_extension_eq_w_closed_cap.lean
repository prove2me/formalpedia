-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:26:55.863673+00:00
-- url     : https://prove2.me/submissions/7491007f-1755-4494-885a-077d80ccf2fb

import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The cap-linear value extension agrees with the candidate at every closed-cap postpayment state, including zero and the cap. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w V : ℝ → ℝ)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z : ℝ) (hz0 : 0 ≤ z) (hzC : ENNReal.ofReal z ≤ C) :
    V z = w z := by
  by_cases htop : C = ⊤
  · exact hVtop htop z
  · have hReal : z ≤ C.toReal := by
      have h := ENNReal.toReal_mono htop hzC
      rw [ENNReal.toReal_ofReal hz0] at h
      exact h
    rw [hVfinite htop z]
    exact if_pos hReal
