-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin17_original_bounded_band_compensated_stopped_martingale_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:20:16.664848+00:00
-- url     : https://prove2.me/submissions/f8dedf15-3e30-4ae3-8e6b-44f1a21a4ae3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_j18_original_bounded_band_cadlag_dominated_martingale
import Theorems.Thm_AvramDividend_Classical_avram_j18_original_bounded_band_rightcont_optional_sampling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Separate the original physical bounded-band martingale from bounded optional sampling. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0)) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
      Integrable (fun ω => Jsmall (τ ω) ω) P ∧
      (∀ᵐ ω ∂P,
        condExp (𝓕.rightCont 0) P
          (fun ω => Jsmall (τ ω) ω) ω = 0) := by
  obtain ⟨Jsmall, B, hLimit, hInt, hMart, hRight, hZero, hBInt, hDom⟩ :=
    avram_j18_original_bounded_band_cadlag_dominated_martingale
      X hX hFinite n hn
  obtain ⟨hStopInt, hStopCenter⟩ :=
    avram_j18_original_bounded_band_rightcont_optional_sampling
      X hX hFinite n hn τ hτstop hτbound
      Jsmall B hInt hMart hRight hZero hBInt hDom
  exact ⟨Jsmall, hLimit, hInt, hMart, hStopInt, hStopCenter⟩
