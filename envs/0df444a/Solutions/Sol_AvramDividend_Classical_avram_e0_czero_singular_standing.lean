-- Prove2me | solution 1 for AvramDividend.Classical.avram_e0_czero_singular_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:52:54.252489+00:00
-- url     : https://prove2.me/submissions/7a25b12f-6a9e-4820-b298-26ef60dd2c62

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_restricted_signed_moment_neg_two
import Theorems.Thm_AvramDividend_Classical_avram_e0_singular_czero_drift_eq_two
import Theorems.Thm_AvramDividend_Classical_avram_e0_standing_of_positive_drift_singular_density
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Assemble the proved original density, physical drift, and Standing facts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hc : X.c = 0)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hint : Integrable (X.X 1) P) : X.Standing := by
  have hpos : 0 < X.drift := by
    rw [AvramDividend.Classical.avram_e0_singular_czero_drift_eq_two X hc hν]
    norm_num
  have hne : X.ν ≠ 0 := by
    intro hz
    have hm : (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) = -2 := by
      rw [hν]
      exact AvramDividend.Classical.avram_gen15_singular_density_restricted_signed_moment_neg_two
    rw [hz] at hm
    norm_num at hm
  exact AvramDividend.Classical.avram_e0_standing_of_positive_drift_singular_density
    X hν hpos hne hint
