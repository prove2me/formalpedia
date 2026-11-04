-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_stopped_generator_L1_nonpos_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:11:16.290803+00:00
-- url     : https://prove2.me/submissions/08a56132-416a-4e5f-aec7-48facc555821

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The actual nonpositive source BV HJB generator on a stopped physical region has an integrable named drift and nonpositive mean. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [SFinite P] {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
  (T : ℝ≥0) (μT : Measure ℝ≥0) [SFinite μT]
  (hTime : μT = (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))
  (A : Ω → Set ℝ≥0) (hAm : ∀ ω, MeasurableSet (A ω))
  (K : ℝ≥0 → Ω → ℝ)
  (hK : ∀ t ω, K t ω =
    Real.exp (-(q * (t : ℝ))) *
      (X.drift * deriv w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) +
      (∫ z in Iio (0 : ℝ),
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t + z) -
        w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s ω - rightLimit D s ω) t) ∂X.ν) -
      q * w (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t)))
  (F : (ℝ≥0 × Ω) → ℝ)
  (hF : ∀ p, F p = if p.1 ∈ A p.2 then K p.1 p.2 else 0)
  (hFI : Integrable F (μT.prod P))
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT)
  (hKnonpos : ∀ᵐ ω ∂P, ∀ t, t ∈ A ω → K t ω ≤ 0) :
  Integrable Gdrift P ∧
  (∀ᵐ ω ∂P, Gdrift ω ≤ 0) ∧
  (∫ ω, Gdrift ω ∂P) ≤ 0 := by
  classical
  have hBase :=
    avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
      X hBV q w x D T μT hTime A hAm K hK F hF hFI
  have hEq : (fun ω => ∫ t in A ω, K t ω ∂μT) =ᵐ[P] Gdrift := by
    filter_upwards [hGDef] with ω heq
    exact heq.symm
  have hGI : Integrable Gdrift P :=
    hBase.2.1.congr hEq
  have hNonposInt : ∀ᵐ ω ∂P, (∫ t in A ω, K t ω ∂μT) ≤ 0 := by
    filter_upwards [hKnonpos] with ω hh
    have hPt : ∀ t : ℝ≥0, (A ω).indicator (fun s => K s ω) t ≤ 0 := by
      intro t
      by_cases ht : t ∈ A ω
      · simpa [Set.indicator, ht] using hh t ht
      · simp [Set.indicator, ht]
    have hLe := integral_nonpos_of_ae (Filter.Eventually.of_forall hPt : (A ω).indicator (fun s => K s ω) ≤ᵐ[μT] 0)
    rw [integral_indicator (hAm ω)] at hLe
    exact hLe
  have hGNonpos : ∀ᵐ ω ∂P, Gdrift ω ≤ 0 := by
    filter_upwards [hGDef, hNonposInt] with ω heq hle
    rw [heq]
    exact hle
  exact ⟨hGI, hGNonpos, integral_nonpos_of_ae hGNonpos⟩
