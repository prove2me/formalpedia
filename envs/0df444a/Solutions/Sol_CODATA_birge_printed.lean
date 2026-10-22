-- Prove2me | solution 1 for CODATA.birge_printed
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:07:42.873198+00:00
-- url     : https://prove2.me/submissions/d8b1b7d5-5908-45ad-b8d8-d86ccbaac2be

import Mathlib
import Definitions.Def_CODATA_lsa
import Definitions.Def_CODATA_uncert
import Definitions.Def_CODATA_values
/-!
# The printed degrees of freedom and Birge ratios

Section XII of the 2022 CODATA report records the arithmetic of the
two adjustments on which the recommended values are based: the main
adjustment of 133 input data for 79 adjusted constants, with
nu = N - M = 54 degrees of freedom and a final chi-square of 44.2, and
the separate adjustment of the sixteen values of the Newtonian
constant of gravitation, with 16 - 1 = 15 degrees of freedom and
chi-square 12.9; the Birge ratio R_B = sqrt(chi^2/nu) is printed as
0.90 for the main adjustment and 0.93 for the Newtonian constant. This
milestone verifies these printed numbers by exact real arithmetic: the
two subtractions, and the two rounding intervals that the printed
Birge ratios determine. This milestone is proved on the way to the
goal theorem `CODATA.codata_self_consistent`.
-/

open CODATA

/-- The degrees of freedom of the two adjustments of the 2022 CODATA
report are 133 - 79 = 54 and 16 - 1 = 15, and the Birge ratios
sqrt(44.2/54) and sqrt(12.9/15) round to the printed values 0.90 and
0.93: they lie in the intervals [0.895, 0.905) and [0.925, 0.935). -/
theorem solution :
    dof 133 79 = 54 ∧ dof 16 1 = 15 ∧
      895/1000 ≤ Real.sqrt (442/10/54) ∧ Real.sqrt (442/10/54) < 905/1000 ∧
      925/1000 ≤ Real.sqrt (129/10/15) ∧ Real.sqrt (129/10/15) < 935/1000 := by
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num
  · rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num


