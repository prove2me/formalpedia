-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_time_enveloped_generator_L1_and_Fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:10:34.380823+00:00
-- url     : https://prove2.me/submissions/455f9160-71e2-49c5-8e1a-ddb5085f2fe7

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

/-- Original physical-generator product L¹ follows from a genuine integrable deterministic time envelope, then yields original named drift L¹ and Fubini. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
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
  (hFmeas : AEStronglyMeasurable F (μT.prod P))
  (g : ℝ≥0 → ℝ) (hgI : Integrable g μT)
  (hFbound : ∀ᵐ p ∂(μT.prod P), ‖F p‖ ≤ ‖g p.1‖)
  (Gdrift : Ω → ℝ)
  (hGDef : ∀ᵐ ω ∂P, Gdrift ω = ∫ t in A ω, K t ω ∂μT) :
  Integrable F (μT.prod P) ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun t => K t ω) (A ω) μT) ∧
  Integrable Gdrift P ∧
  (∫ ω, Gdrift ω ∂P) =
    (∫ p, F p ∂(μT.prod P)) := by
  have hDom : Integrable (fun p : ℝ≥0 × Ω => g p.1) (μT.prod P) :=
    hgI.comp_fst P
  have hFI : Integrable F (μT.prod P) :=
    hDom.mono hFmeas hFbound
  have hBase :=
    avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
      X hBV q w x D T μT hTime A hAm K hK F hF hFI
  have hEq : (fun ω => ∫ t in A ω, K t ω ∂μT) =ᵐ[P] Gdrift := by
    filter_upwards [hGDef] with ω heq
    exact heq.symm
  have hGI : Integrable Gdrift P :=
    hBase.2.1.congr hEq
  refine ⟨hFI, hBase.1, hGI, ?_⟩
  calc
    (∫ ω, Gdrift ω ∂P) =
        (∫ ω, ∫ t in A ω, K t ω ∂μT ∂P) :=
      integral_congr_ae hGDef
    _ = (∫ p, F p ∂(μT.prod P)) := hBase.2.2
