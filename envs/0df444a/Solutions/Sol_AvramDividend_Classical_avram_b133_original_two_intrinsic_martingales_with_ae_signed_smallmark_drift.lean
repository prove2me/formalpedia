-- Prove2me | solution 1 for AvramDividend.Classical.avram_b133_original_two_intrinsic_martingales_with_ae_signed_smallmark_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:35:03.388197+00:00
-- url     : https://prove2.me/submissions/591442e9-9b9a-43ee-ade3-ea45d7f144e6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
import Theorems.Thm_AvramDividend_Classical_avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the original Levy space both physical intrinsic source martingales exist, and the smallmark channel has exact conull compensated drift under the original cutoff identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
    (s t : Ω → ℝ≥0)
    (hCut : ∀ᵐ ω ∂P, ∀ k : ℕ,
      avram_p4_h_gaussian_intrinsic_small_band_compensated X k (t ω) ω -
        avram_p4_h_gaussian_intrinsic_small_band_compensated X k (s ω) ω =
      ((t ω : ℝ) - (s ω : ℝ)) *
        (-(∫ z in Ioc (-1 : ℝ) (-(1 / ((k : ℝ) + 1))), z ∂X.ν))) :
    ∃ (R Jsmall : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
        atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto
        (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
        atTop (𝓝 (Jsmall u ω))) ∧
      (∀ u : ℝ≥0, Integrable (R u) P) ∧
      (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
      (∀ᵐ ω ∂P, Jsmall (t ω) ω - Jsmall (s ω) ω =
        -(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν) *
          ((t ω : ℝ) - (s ω : ℝ))) := by
  obtain ⟨R, Jsmall, MG, MJ, hRsrc, hJsrc, hRint, hRmart,
      hJint, hJmart, _⟩ :=
    avram_b32_original_finite_range_two_intrinsic_centered_sources_exist
      X hX hFinite n hn τ hτstop hτbound S hτrange
  refine ⟨R, Jsmall, hRsrc, hJsrc, hRint, hJint, hRmart, hJmart, ?_⟩
  exact avram_b127_original_ae_smallmark_cutoff_drift_limit_transfer
    X hFinite Jsmall hJsrc s t hCut
