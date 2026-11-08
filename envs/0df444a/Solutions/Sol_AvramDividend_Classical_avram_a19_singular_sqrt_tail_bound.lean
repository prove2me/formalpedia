-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_sqrt_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:44:47.697827+00:00
-- url     : https://prove2.me/submissions/052e4c56-d3e8-4aba-aa73-95eadf84c28c

import Mathlib.Analysis.Real.Sqrt
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_profile_tail_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- A positive near-zero surplus amplifies the singular generator loss. -/
theorem solution (y : Real) (hy : 0 < y) (hsmall : y <= 1 / 16) :
    1 / Real.sqrt y <=
      -(3 + y - 4 * Real.sqrt y - 2 / Real.sqrt y) := by
  have hspos : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hsq : (Real.sqrt y) ^ 2 = y :=
    Real.sq_sqrt (le_of_lt hy)
  have hroot_small : Real.sqrt y <= 1 / 4 := by
    by_contra h
    have hgt : (1 : Real) / 4 < Real.sqrt y := lt_of_not_ge h
    have hp : 0 < (Real.sqrt y - 1 / 4) *
        (Real.sqrt y + 1 / 4) :=
      mul_pos (sub_pos.mpr hgt) (by linarith)
    nlinarith
  have htail :=
    AvramDividend.Classical.avram_a19_singular_profile_tail_bound
      (Real.sqrt y) hspos hroot_small
  simpa [hsq] using htail
