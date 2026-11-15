-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB35_original_gaussian_caplinear_offkink_HJB_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:38:08.161067+00:00
-- url     : https://prove2.me/submissions/15317681-0173-4044-a241-a91d5ec66267

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_gaussian_caplinear_upper_generator_eq_drift
import Theorems.Thm_AvramDividend_Classical_avram_gbB34_original_gaussian_caplinear_lower_generator_eq_original
import Theorems.Thm_AvramDividend_Classical_avram_gfinite59_caplinear_affine_discount_drift_le_positive_part
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (b q : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0)
    (y : ℝ) (hy : 0 < y) (hne : y ≠ b) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    X.generator V y - q * V y ≤
      if b < y then max X.c 0 else 0 := by
  let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
  change X.generator V y - q * V y ≤
    if b < y then max X.c 0 else 0
  by_cases hby : b < y
  · have hg :=
      (avram_gbB32_original_gaussian_caplinear_upper_generator_eq_drift
        X hν w b y hby).2
    have hv : V y = w b + (y - b) := by simp [V, not_le.mpr hby]
    rw [if_pos hby, hg, hv]
    exact avram_gfinite59_caplinear_affine_discount_drift_le_positive_part
      X.c q (w b) b y hq hwb (le_of_lt hby)
  · have hyb : y < b := lt_of_le_of_ne (le_of_not_gt hby) hne
    have hg :=
      avram_gbB34_original_gaussian_caplinear_lower_generator_eq_original
        X hν w b y hyb
    have hv : V y = w y := by simp [V, le_of_lt hyb]
    rw [if_neg hby, hg, hv]
    exact hHJB y hy hyb
