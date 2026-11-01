-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_hjb_all_cap_of_ruin_band_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:44:54.245991+00:00
-- url     : https://prove2.me/submissions/bd97e723-6399-4916-b15d-4fd0ca9b6fa4

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_hjb_all_cap_of_ruin_overshoot_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_ruin_overshoot_integral_le_band_mass_of_levy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A finite-band mass inequality suffices for upper HJB at every source
optimal cap, zero included; the source itself supplies jump integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (hmass : X.c +
        (X.ν).real (Ioo (-1 : ℝ) (-x)) * max 0 (1 - vcstar W x) ≤
        q * vcstar W x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hx0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  have hsub : Ioo (-1 : ℝ) (-x) ⊆ Iio (0 : ℝ) := by
    intro y hy
    exact lt_trans hy.2 (neg_lt_zero.mpr hx0)
  have hinter : Iio (0 : ℝ) ∩ Ioo (-1 : ℝ) (-x) =
      Ioo (-1 : ℝ) (-x) := Set.inter_eq_right.mpr hsub
  have heq :
      (∫ y in Iio (0 : ℝ),
        (Ioo (-1 : ℝ) (-x)).indicator
          (fun z : ℝ => max 0 (-vcstar W x - z)) y ∂X.ν) =
      ∫ y in Ioo (-1 : ℝ) (-x),
        max 0 (-vcstar W x - y) ∂X.ν := by
    rw [setIntegral_indicator measurableSet_Ioo]
    rw [hinter]
  have hband := avram_wave4_05_source_ruin_overshoot_integral_le_band_mass_of_levy
    X W x hx0
  have hbound : X.c +
      (∫ y in Iio (0 : ℝ),
        (Ioo (-1 : ℝ) (-x)).indicator
          (fun z : ℝ => max 0 (-vcstar W x - z)) y ∂X.ν) ≤
        q * vcstar W x := by
    rw [heq]
    linarith
  exact avram_wave4_05_source_hjb_all_cap_of_ruin_overshoot_bound
    X hX q hq W hW x hx hbound
