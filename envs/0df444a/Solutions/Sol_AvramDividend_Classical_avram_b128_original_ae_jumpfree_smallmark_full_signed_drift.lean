-- Prove2me | solution 1 for AvramDividend.Classical.avram_b128_original_ae_jumpfree_smallmark_full_signed_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:54:03.274945+00:00
-- url     : https://prove2.me/submissions/663f445c-00ff-4725-bb15-9fe1473f43b1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original jump-free random clock increments retain only the full signed compensation drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto
        (fun n : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ᵐ ω ∂P,
      Jsmall (t ω) ω - Jsmall (s ω) ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
          ((t ω : ℝ) - (s ω : ℝ)) := by
  have hNu :=
    avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
      X hFinite
  filter_upwards [hJlim, hNoJump] with ω hJω hNoω
  let delta : ℝ := (t ω : ℝ) - (s ω : ℝ)
  have hCell (n : ℕ) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω =
        -delta * (∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν) := by
    exact avram_b80_original_jumpfree_cell_smallband_compensator_increment
      X n (s ω) (t ω) (hOrder ω) ω hNoω
  have hFirst := (hJω (t ω)).sub (hJω (s ω))
  have hSecond : Tendsto
      (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω)
      atTop
      (𝓝 (-delta * (∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) := by
    have hh := (tendsto_const_nhds (x := -delta)).mul hNu
    convert hh using 1
    funext n
    exact hCell n
  have hEq := tendsto_nhds_unique hFirst hSecond
  dsimp [delta] at hEq
  nlinarith [hEq]
