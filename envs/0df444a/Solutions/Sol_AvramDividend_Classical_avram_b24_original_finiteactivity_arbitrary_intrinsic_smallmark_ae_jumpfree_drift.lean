-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_original_finiteactivity_arbitrary_intrinsic_smallmark_ae_jumpfree_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:45:06.489833+00:00
-- url     : https://prove2.me/submissions/4f58162e-533c-4977-8070-3847728f9c3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (Jsmall : ℝ≥0 → Ω → ℝ)
    (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0)
    (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∀ᵐ ω ∂P, Jsmall (t ω) ω - Jsmall (s ω) ω =
      -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
        ((t ω : ℝ) - (s ω : ℝ)) := by
  have hMoment :=
    avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
      X hFinite
  have hNeg : Tendsto (fun n : ℕ =>
      -(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
      atTop (𝓝 (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν))) :=
    hMoment.neg
  filter_upwards [hJsource, hNoJump] with ω hLimω hNoω
  have hCut (k : ℕ) :
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k (s ω) ω =
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1))), z ∂X.ν)) := by
    have h :=
      avram_b80_original_jumpfree_cell_smallband_compensator_increment
        X k (s ω) (t ω) (hOrder ω) ω hNoω
    rw [h]
    ring
  have hSourceLimit : Tendsto (fun k : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k (s ω) ω)
      atTop (𝓝 (Jsmall (t ω) ω - Jsmall (s ω) ω)) :=
    (hLimω (t ω)).sub (hLimω (s ω))
  have hLimitMoment : Tendsto (fun k : ℕ =>
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1))), z ∂X.ν)))
      atTop (𝓝 (((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)))) :=
    tendsto_const_nhds.mul hNeg
  have hSeq : (fun k : ℕ =>
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k (s ω) ω) =
      (fun k : ℕ => ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1))), z ∂X.ν))) := by
    funext k
    exact hCut k
  rw [hSeq] at hSourceLimit
  have hEq := tendsto_nhds_unique hSourceLimit hLimitMoment
  nlinarith
