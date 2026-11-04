-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_stopped_generator_product_L1_all_fibre_and_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:14:04.062083+00:00
-- url     : https://prove2.me/submissions/45733732-837b-46d0-88b1-84dfbfef246f

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_stopped_physical_generator_restricted_time_fubini
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The original BV physical stopped product L¹ simultaneously gives a.e. physical time-fibre L¹, the random stopped generator L¹, and its Fubini mean. -/
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
  (hFI : Integrable F (μT.prod P)) :
  (∀ᵐ ω ∂P, IntegrableOn (fun t => K t ω) (A ω) μT) ∧
  Integrable (fun ω => ∫ t in A ω, K t ω ∂μT) P ∧
  (∫ ω, ∫ t in A ω, K t ω ∂μT ∂P) =
    (∫ p, F p ∂(μT.prod P))  := by
  classical
  have hFibre : ∀ᵐ ω ∂P, IntegrableOn (fun t => K t ω) (A ω) μT := by
    filter_upwards [hFI.prod_left_ae] with ω hFIω
    have hFω : (fun t => F (t, ω)) =
        (A ω).indicator (fun t => K t ω) := by
      funext t
      by_cases ht : t ∈ A ω
      · simp [hF, Set.indicator, ht]
      · simp [hF, Set.indicator, ht]
    rw [hFω] at hFIω
    exact (integrable_indicator_iff (hAm ω)).mp hFIω
  have hTransport :=
    avram_wave8_22_original_BV_stopped_physical_generator_restricted_time_fubini
      X hBV q w x D T μT hTime A hAm K hK F hF hFI
  exact ⟨hFibre, hTransport.1, hTransport.2⟩
