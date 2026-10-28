-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_stoppedHistory_lintegral_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T19:12:36.319006+00:00
-- url     : https://prove2.me/submissions/5744875b-b1e5-4eb2-8315-705ec09ec2fb

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_observable_map_law
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (T : ℝ≥0) (hT : H + 1 ≤ T)
    (F : Ω → ℝ≥0∞) (hF : Measurable F)
    (hFstopped : ∀ (B : Set ℝ≥0∞), MeasurableSet B →
      ∀ s : ℝ≥0, MeasurableSet[𝓕 s]
        ((F ⁻¹' B) ∩ {ω : Ω | τ ω ≤ s})) :
    ∫⁻ ω, F ω ∂(P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) =
    ∫⁻ ω, F ω ∂(P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))) := by
  let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
  let QStop : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
    (Real.exp (θ * X.X (τ ω) ω -
      (τ ω : ℝ) * X.ψ θ)))
  have hmap : Measure.map F QT = Measure.map F QStop :=
    esscher_bounded_stop_stoppedHistory_observable_map_law
      X θ hθ τ hstop H hbound T hT F hF hFstopped
  change ∫⁻ ω, F ω ∂QT = ∫⁻ ω, F ω ∂QStop
  calc
    ∫⁻ ω, F ω ∂QT =
      ∫⁻ z : ℝ≥0∞, z ∂Measure.map F QT := by
        simpa only [id_eq] using
          (lintegral_map (f := id) (g := F) measurable_id hF).symm
    _ = ∫⁻ z : ℝ≥0∞, z ∂Measure.map F QStop := by
        rw [hmap]
    _ = ∫⁻ ω, F ω ∂QStop := by
        simpa only [id_eq] using
          (lintegral_map (f := id) (g := F) measurable_id hF)
