-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_spatial_upcross_fullmark_initial_positive_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T21:56:01.048276+00:00
-- url     : https://prove2.me/submissions/8ebfad15-7a0b-43ec-a368-3613debc62ae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_fullmark_stopped_jump_initial_event_integral_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The actual compensated full jump source cancels at a spatial stopped clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R Jsmall : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hJ : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
        atTop (nhds (Jsmall t ω)))
    (hRint : ∀ t : ℝ≥0, Integrable (R t) P)
    (hRmart : ∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P, condExp (𝓕.rightCont s) P (R t) ω = R s ω)
    (n : ℕ) (hn : 0 < n)
    (κ : ℕ → Ω → ℝ≥0)
    (hκstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (κ k ω : WithTop ℝ≥0)))
    (hκbound : ∀ k ω, κ k ω ≤ (n : ℝ≥0))
    (k : ℕ) (A : Set Ω)
    (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ Jfull : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) ∧
      Integrable (fun ω => Jfull (κ k ω) ω) P ∧
      (∫ ω in A ∩ {η : Ω | κ k η ≠ 0}, Jfull (κ k ω) ω ∂P) = 0 := by
  have hPositive :
      MeasurableSet[𝓕.rightCont 0] {η : Ω | κ k η ≠ 0} :=
    avram_ubv_finite12_positive_clock_initial_measurable
      (κ k) (hκstop k)
  have hEvent : MeasurableSet[𝓕.rightCont 0]
      (A ∩ {η : Ω | κ k η ≠ 0}) := hA.inter hPositive
  exact avram_ja18_original_fullmark_stopped_jump_initial_event_integral_zero
    X hX hFinite R Jsmall hR hJ hRint hRmart
    n hn (κ k) (hκstop k) (hκbound k)
    (A ∩ {η : Ω | κ k η ≠ 0}) hEvent
