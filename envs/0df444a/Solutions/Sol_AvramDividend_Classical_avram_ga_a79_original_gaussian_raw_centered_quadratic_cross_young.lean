-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a79_original_gaussian_raw_centered_quadratic_cross_young
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:06:40.074563+00:00
-- url     : https://prove2.me/submissions/5d7655a5-5ea6-4d52-b755-fa9ba5431c48

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a84_centered_gaussian_quadratic_cross_young_product
import Theorems.Thm_AvramDividend_Classical_avram_ga_a85_gaussian_raw_centered_square_triangle
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical

/-- The actual raw/centred Gaussian quadratic cross term is arbitrarily small relative to centred energy plus a drift-squared correction. -/
theorem solution (z d ε : ℝ) (hε : 0 < ε) :
    |(z + d)^2 - z^2| ≤ ε * z^2 + (1 + 1 / ε) * d^2 := by
  calc
    |(z + d)^2 - z^2| ≤ 2 * |d| * |z| + d^2 :=
      avram_ga_a85_gaussian_raw_centered_square_triangle z d
    _ ≤ ε * z^2 + d^2 / ε + d^2 :=
      add_le_add
        (avram_ga_a84_centered_gaussian_quadratic_cross_young_product z d ε hε)
        (le_refl _)
    _ = ε * z^2 + (1 + 1 / ε) * d^2 := by ring
