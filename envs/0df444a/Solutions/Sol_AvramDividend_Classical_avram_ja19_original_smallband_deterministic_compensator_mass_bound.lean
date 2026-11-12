-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja19_original_smallband_deterministic_compensator_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:21:31.363208+00:00
-- url     : https://prove2.me/submissions/14503b77-3a1a-44fd-a419-2d38290fb1b5

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (T : ℝ≥0) (k : ℕ) (t : ℝ≥0), t ≤ T →
      |(t : ℝ) * (∫ z in Ioc (-1 : ℝ)
          (-(1 / ((k : ℝ) + 1))), z ∂X.ν)| ≤
        (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by
  intro T k t ht
  let band : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1)))
  have hneg : -(1 / ((k : ℝ) + 1)) < 0 := by
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hp : (0 : ℝ) < 1 / ((k : ℝ) + 1) := div_pos (by norm_num) hk
    linarith
  have hsub : band ⊆ Iio (0 : ℝ) := by
    intro z hz
    exact lt_of_le_of_lt hz.2 hneg
  have hbandFinite : X.ν band < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) (lt_top_iff_ne_top.mpr hFinite)
  have hbound : ∀ z ∈ band, ‖z‖ ≤ (1 : ℝ) := by
    intro z hz
    rw [Real.norm_eq_abs, abs_of_nonpos (le_of_lt (lt_of_le_of_lt hz.2 hneg))]
    linarith [hz.1]
  have hint : ‖∫ z in band, z ∂X.ν‖ ≤ (X.ν band).toReal := by
    simpa only [one_mul, measureReal_def] using
      (norm_setIntegral_le_of_norm_le_const (μ := X.ν)
        (f := fun z : ℝ => z) hbandFinite hbound)
  have hmass : (X.ν band).toReal ≤ (X.ν (Iio (0 : ℝ))).toReal :=
    ENNReal.toReal_mono hFinite (measure_mono hsub)
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.property
  have htT : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
  calc
    |(t : ℝ) * (∫ z in band, z ∂X.ν)| =
        (t : ℝ) * ‖∫ z in band, z ∂X.ν‖ := by
          rw [abs_mul, abs_of_nonneg ht0, Real.norm_eq_abs]
    _ ≤ (t : ℝ) * (X.ν band).toReal :=
      mul_le_mul_of_nonneg_left hint ht0
    _ ≤ (T : ℝ) * (X.ν (Iio (0 : ℝ))).toReal := by
      exact (mul_le_mul_of_nonneg_left hmass ht0).trans
        (mul_le_mul_of_nonneg_right htT ENNReal.toReal_nonneg)
