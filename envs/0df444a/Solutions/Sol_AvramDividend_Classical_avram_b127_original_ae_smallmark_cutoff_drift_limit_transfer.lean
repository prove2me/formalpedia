-- Prove2me | solution 1 for AvramDividend.Classical.avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:26:13.548205+00:00
-- url     : https://prove2.me/submissions/4528bfb1-0698-4091-97c3-74d198d73c9c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the true original conull event, finite negative-band compensation identities converge to the full signed small-mark physical drift. -/
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
    (s t : Ω → ℝ≥0)
    (hCut : ∀ᵐ ω ∂P, ∀ n : ℕ,
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω =
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))) :
    ∀ᵐ ω ∂P,
      Jsmall (t ω) ω - Jsmall (s ω) ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
          ((t ω : ℝ) - (s ω : ℝ)) := by
  have hMoment :=
    avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
      X hFinite
  have hNeg : Tendsto (fun n : ℕ =>
      -(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) :=
    hMoment.neg
  filter_upwards [hJlim, hCut] with ω hωlim hωcut
  have hSource : Tendsto (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω)
      atTop (𝓝 (Jsmall (t ω) ω - Jsmall (s ω) ω)) :=
    (hωlim (t ω)).sub (hωlim (s ω))
  have hDrift : Tendsto (fun n : ℕ =>
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)))
      atTop (𝓝 (((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)))) :=
    tendsto_const_nhds.mul hNeg
  have hSeq : (fun n : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω) =
      (fun n : ℕ => ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))) := by
    funext n
    exact hωcut n
  rw [hSeq] at hSource
  have hEq := tendsto_nhds_unique hSource hDrift
  nlinarith
