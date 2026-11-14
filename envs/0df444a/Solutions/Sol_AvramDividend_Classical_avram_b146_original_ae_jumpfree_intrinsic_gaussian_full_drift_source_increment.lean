-- Prove2me | solution 1 for AvramDividend.Classical.avram_b146_original_ae_jumpfree_intrinsic_gaussian_full_drift_source_increment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:42:56.04294+00:00
-- url     : https://prove2.me/submissions/0b79ad28-9b07-4983-8294-4ed80f3147b5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_jb20_original_physical_random_clock_increment_split
import Theorems.Thm_AvramDividend_Classical_avram_b80_original_jumpfree_cell_smallband_compensator_increment
import Theorems.Thm_AvramDividend_Classical_avram_b81_original_jumpfree_cell_large_mark_sum_constant
import Theorems.Thm_AvramDividend_Classical_avram_b84_original_finite_activity_negative_mark_cutoff_integral_limit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original source increment on conull physical jumpfree stopped intervals equals intrinsic Gaussian residual plus its exact full negative-strip signed drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω)))
    (hJlim : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω)))
    (s t : Ω → ℝ≥0) (hOrder : ∀ ω, s ω ≤ t ω)
    (hNoJump : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, s ω < u → u ≤ t ω →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) ∧
      (∀ᵐ ω ∂P, X.X (t ω) ω - X.X (s ω) ω =
        ((t ω : ℝ) - (s ω : ℝ)) *
          (X.c - ∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) +
        (R (t ω) ω - R (s ω) ω)) := by
  obtain ⟨M, hFull, hMsource, hClocks, hMatch⟩ :=
    avram_jb20_original_physical_random_clock_increment_split
      X R Jsmall hRsource hJlim
  refine ⟨M, hFull, ?_⟩
  have hSigned : ∀ᵐ ω ∂P,
      Jsmall (t ω) ω - Jsmall (s ω) ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
          ((t ω : ℝ) - (s ω : ℝ)) := by
    have hCut : ∀ᵐ ω ∂P, ∀ n : ℕ,
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (t ω) ω -
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n (s ω) ω =
        ((t ω : ℝ) - (s ω : ℝ)) *
          (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1))), z ∂X.ν)) := by
      filter_upwards [hNoJump] with ω hω
      intro n
      have h :=
        avram_b80_original_jumpfree_cell_smallband_compensator_increment
          X n (s ω) (t ω) (hOrder ω) ω hω
      rw [h]
      ring
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
  have hMatchClocks := hMatch s t
  filter_upwards [hNoJump, hSigned, hMatchClocks] with ω hωnojump hωsigned hωmatch
  have hLarge :=
    avram_b81_original_jumpfree_cell_large_mark_sum_constant
      X (s ω) (t ω) (hOrder ω) ω hωnojump
  have hSource := hClocks s t ω
  rw [sub_eq_zero.mpr hLarge, hωsigned, hωmatch] at hSource
  nlinarith [hSource]
