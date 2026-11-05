-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_finite_cap_full_source_increment_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:11:44.757875+00:00
-- url     : https://prove2.me/submissions/00d707d4-645c-4218-a5b7-8c69a129ff8d

import Mathlib.Data.ENNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal

theorem solution
    (C : ℝ≥0∞) (hCfinite : C ≠ ⊤) (w V : ℝ → ℝ)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (z d : ℝ) :
    V (z + d) - V z =
      (w (min (z + d) C.toReal) - w (min z C.toReal)) +
        (max (z + d - C.toReal) 0 - max (z - C.toReal) 0) := by
  have hV : ∀ t : ℝ, V t = if t ≤ C.toReal then w t
      else w C.toReal + (t - C.toReal) := hVfinite hCfinite
  have hVrepr (t : ℝ) :
      V t = w (min t C.toReal) + max (t - C.toReal) 0 := by
    by_cases ht : t ≤ C.toReal
    · rw [hV t, if_pos ht, min_eq_left ht,
          max_eq_right (sub_nonpos.mpr ht)]
      ring
    · have hct : C.toReal ≤ t := le_of_lt (lt_of_not_ge ht)
      rw [hV t, if_neg ht, min_eq_right hct,
          max_eq_left (sub_nonneg.mpr hct)]
  rw [hVrepr (z + d), hVrepr z]
  ring
