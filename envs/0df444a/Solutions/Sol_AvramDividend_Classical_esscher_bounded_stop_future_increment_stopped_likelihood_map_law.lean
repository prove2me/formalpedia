-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_future_increment_stopped_likelihood_map_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T18:57:55.805522+00:00
-- url     : https://prove2.me/submissions/6d79dc4f-a75c-4c2f-9657-b2c305164ccc

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_map_law
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_stoppedHistory_density_eq
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
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s})) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let QStop : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω - X.X (τ ω) ω)
      (QT.restrict A) = QStop A • Measure.map (X.X u) QU := by
  intro QT QU QStop
  have hT' : H + 1 ≤ T := by
    calc
      H + 1 ≤ H + 1 + u :=
        le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ u from bot_le)
      _ ≤ T := hT
  have hHistory : QT A = QStop A :=
    esscher_bounded_stop_stoppedHistory_density_eq
      X θ hθ τ hstop H hbound T hT' A hA
  calc
    Measure.map (fun ω : Ω => X.X (τ ω + u) ω -
        X.X (τ ω) ω) (QT.restrict A) =
      QT A • Measure.map (X.X u) QU :=
        esscher_bounded_stop_future_increment_map_law
          X θ hθ τ hstop H hbound u T hT A hA
    _ = QStop A • Measure.map (X.X u) QU := by
      rw [hHistory]

