-- Prove2me | solution 1 for AvramDividend.Classical.avram_b67_original_preupper_X_centered_cell_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:37:18.921495+00:00
-- url     : https://prove2.me/submissions/d1acd8e9-3750-4e99-8f72-96493bfb1452

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin22_original_strict_pre_upper_clock_value_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine original bounded pre-exit source increments have a source-drift corrected compact bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x b : ℝ) (T : ℝ≥0)
    (ω : Ω) (s t : ℝ≥0)
    (hst : s ≤ t) (htT : t ≤ T)
    (hsLower : -x ≤ X.X s ω) (htLower : -x ≤ X.X t ω)
    (hsExit : (s : ℝ≥0∞) < twoSidedExitUpTime X b ω)
    (htExit : (t : ℝ≥0∞) < twoSidedExitUpTime X b ω) :
    |X.X t ω - X.X s ω -
      ((t - s : ℝ≥0) : ℝ) * X.c| ≤
      x + b + (T : ℝ) * |X.c| := by
  have hsUpper : X.X s ω ≤ b :=
    avram_mix_fin22_original_strict_pre_upper_clock_value_le X b ω s hsExit
  have htUpper : X.X t ω ≤ b :=
    avram_mix_fin22_original_strict_pre_upper_clock_value_le X b ω t htExit
  have hDiff : |X.X t ω - X.X s ω| ≤ x + b := by
    apply abs_le.mpr
    constructor <;> linarith
  have hTime : ((t - s : ℝ≥0) : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast ((tsub_le_self : t - s ≤ t).trans htT)
  have hTimePos : 0 ≤ ((t - s : ℝ≥0) : ℝ) := NNReal.coe_nonneg (t - s)
  have hTriangle :
      |X.X t ω - X.X s ω -
        ((t - s : ℝ≥0) : ℝ) * X.c| ≤
        |X.X t ω - X.X s ω| +
        |((t - s : ℝ≥0) : ℝ) * X.c| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      (abs_sub_le (X.X t ω - X.X s ω) 0 (((t - s : ℝ≥0) : ℝ) * X.c))
  calc
    |X.X t ω - X.X s ω -
        ((t - s : ℝ≥0) : ℝ) * X.c| ≤
          |X.X t ω - X.X s ω| +
            |((t - s : ℝ≥0) : ℝ) * X.c| := hTriangle
    _ ≤ x + b + |((t - s : ℝ≥0) : ℝ) * X.c| :=
      by nlinarith [hDiff]
    _ = x + b + ((t - s : ℝ≥0) : ℝ) * |X.c| := by
      rw [abs_mul, abs_of_nonneg hTimePos]
    _ ≤ x + b + (T : ℝ) * |X.c| := by
      nlinarith [mul_le_mul_of_nonneg_right hTime (abs_nonneg X.c)]
