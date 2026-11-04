-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_BV_stopped_physical_generator_restricted_time_fubini
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:07:23.713426+00:00
-- url     : https://prove2.me/submissions/38b217b5-ee71-4dd5-b118-2cb78b013cb5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The exact original BV physical signed generator on an adapted stopped time region has an L¹ random integral and a Fubini expectation identity. -/
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
  Integrable (fun ω => ∫ t in A ω, K t ω ∂μT) P ∧
    (∫ ω, ∫ t in A ω, K t ω ∂μT ∂P) =
      (∫ p, F p ∂(μT.prod P)) := by
  classical
  have hEq (ω : Ω) :
      (∫ t in A ω, K t ω ∂μT) = ∫ t, F (t, ω) ∂μT := by
    have hFω : (fun t => F (t, ω)) =
        (A ω).indicator (fun t => K t ω) := by
      funext t
      by_cases ht : t ∈ A ω
      · simp [hF, Set.indicator, ht]
      · simp [hF, Set.indicator, ht]
    rw [hFω]
    exact (integral_indicator (hAm ω)).symm
  have hRandom : Integrable (fun ω => ∫ t, F (t, ω) ∂μT) P :=
    hFI.integral_prod_right
  have hGI : Integrable (fun ω => ∫ t in A ω, K t ω ∂μT) P :=
    hRandom.congr (Filter.Eventually.of_forall (fun ω => (hEq ω).symm))
  refine ⟨hGI, ?_⟩
  calc
    (∫ ω, ∫ t in A ω, K t ω ∂μT ∂P) =
        (∫ ω, ∫ t, F (t, ω) ∂μT ∂P) :=
      integral_congr_ae (Filter.Eventually.of_forall hEq)
    _ = (∫ p, F p ∂(μT.prod P)) := (integral_prod_symm F hFI).symm
