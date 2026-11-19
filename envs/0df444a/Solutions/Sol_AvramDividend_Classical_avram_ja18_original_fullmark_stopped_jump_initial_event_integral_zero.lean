-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18_original_fullmark_stopped_jump_initial_event_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:29:28.255361+00:00
-- url     : https://prove2.me/submissions/5fe033b8-a271-4d7a-84bf-e9b61897d796

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_finiteactivity_fullmark_stopped_martingale_physical_identification
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/-- The true full negative-mark source is centred over initial information events. -/
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
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    ∃ Jfull : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Jfull t ω =
          Jsmall t ω + avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          (t : ℝ) * (X.c - ∫ ω, X.X 1 ω ∂P)) ∧
      Integrable (fun ω => Jfull (τ ω) ω) P ∧
      (∫ ω in A, Jfull (τ ω) ω ∂P) = 0 := by
  obtain ⟨Jfull, hSource, hJI, hMart, hStopI, hStopZero⟩ :=
    avram_ja18_original_finiteactivity_fullmark_stopped_martingale_physical_identification
      X hX hFinite R Jsmall hR hJ hRint hRmart n hn τ hτstop hτbound
  refine ⟨Jfull, ?_, hStopI, ?_⟩
  · simpa only using hSource
  · exact avram_ubv_jump11_past_event_integral_of_condexp_zero
      (𝓕.rightCont 0) (𝓕.rightCont.le 0)
      (fun ω => Jfull (τ ω) ω) hStopI hStopZero A hA
