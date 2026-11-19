-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_original_fixedj9_caplinear_exact_upper_band_and_cap_defect
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T07:28:12.029142+00:00
-- url     : https://prove2.me/submissions/34912993-de8e-49da-b012-5f950932e7e1

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.NormNum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped ENNReal
noncomputable section
/-- Exact B52 j=9 upper-band and cap-reward mismatch constants. -/
theorem solution :
    let C : ℝ≥0∞ := ENNReal.ofReal (1 / 8 : ℝ)
    let j : ℕ := 9
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    let w : ℝ → ℝ := fun y =>
      if y < 0 then 0 else 2 * y - 4 * y ^ 2
    b = (5 / 44 : ℝ) ∧
      ((w C.toReal - w b) - (C.toReal - b)) =
        (1 / 1936 : ℝ) := by
  dsimp
  norm_num [ENNReal.toReal_ofReal]
