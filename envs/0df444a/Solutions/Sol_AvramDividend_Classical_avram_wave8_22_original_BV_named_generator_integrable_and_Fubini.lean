-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_named_generator_integrable_and_Fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:10:37.34893+00:00
-- url     : https://prove2.me/submissions/d267eff3-952c-4804-b263-64bee34133ed

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

/-- Original named physical generator random variable inherits stopped-fibre and expected Fubini from the actual source clock. -/
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
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT) :
  (∀ᵐ ω ∂P, IntegrableOn (fun t => K t ω) (A ω) μT) ∧
  Integrable Gdrift P ∧
  (∫ ω, Gdrift ω ∂P) =
    (∫ p, F p ∂(μT.prod P)) := by
  have hBase :=
    avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
      X hBV q w x D T μT hTime A hAm K hK F hF hFI
  have hEq : (fun ω => ∫ t in A ω, K t ω ∂μT) =ᵐ[P] Gdrift := by
    filter_upwards [hGDef] with ω heq
    exact heq.symm
  have hGInt : Integrable Gdrift P :=
    hBase.2.1.congr hEq
  refine ⟨hBase.1, hGInt, ?_⟩
  calc
    (∫ ω, Gdrift ω ∂P) =
        (∫ ω, ∫ t in A ω, K t ω ∂μT ∂P) :=
      integral_congr_ae hGDef
    _ = (∫ p, F p ∂(μT.prod P)) := hBase.2.2
