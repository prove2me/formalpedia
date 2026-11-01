-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_all_cap_positive_compensator_integral_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:44:14.116667+00:00
-- url     : https://prove2.me/submissions/8e9cde04-0c92-43ea-88fb-5579a07aaf74

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_all_cap_positive_jump_part_exact

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The entire positive part of the compensated jump integral is exactly
the strict small-ruin overshoot integral, including zero-cap candidates. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : (cstar W).toReal < x) :
    (∫ y in Iio (0 : ℝ),
      max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) ∂X.ν) =
    ∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν := by
  let J : ℝ → ℝ := (Ioo (-1 : ℝ) (-x)).indicator
    (fun y : ℝ => max 0 (-vcstar W x - y))
  have hx0 : 0 < x := lt_of_le_of_lt ENNReal.toReal_nonneg hx
  have hsub : Ioo (-1 : ℝ) (-x) ⊆ Iio (0 : ℝ) := by
    intro y hy
    exact lt_trans hy.2 (neg_lt_zero.mpr hx0)
  have hinter : Iio (0 : ℝ) ∩ Ioo (-1 : ℝ) (-x) =
      Ioo (-1 : ℝ) (-x) := Set.inter_eq_right.mpr hsub
  have hpoint :
      (∫ y in Iio (0 : ℝ),
        max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) ∂X.ν) =
      ∫ y in Iio (0 : ℝ), J y ∂X.ν := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    have heq := avram_wave4_05_source_all_cap_positive_jump_part_exact
      X hX q hq W hW x hx y hy
    rw [heq]
    by_cases hcross : y ∈ Ioo (-1 : ℝ) (-x)
    · simp [J, hcross, Set.indicator_of_mem hcross]
    · simp [J, hcross, Set.indicator_of_notMem hcross]
  calc
    (∫ y in Iio (0 : ℝ),
      max 0 (SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y) ∂X.ν) =
        ∫ y in Iio (0 : ℝ), J y ∂X.ν := hpoint
    _ = ∫ y in Ioo (-1 : ℝ) (-x), max 0 (-vcstar W x - y) ∂X.ν := by
      dsimp [J]
      rw [setIntegral_indicator measurableSet_Ioo]
      rw [hinter]
