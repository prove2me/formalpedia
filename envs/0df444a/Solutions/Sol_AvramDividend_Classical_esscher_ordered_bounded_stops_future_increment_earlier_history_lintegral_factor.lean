-- Prove2me | solution 1 for AvramDividend.Classical.esscher_ordered_bounded_stops_future_increment_earlier_history_lintegral_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:07:00.328979+00:00
-- url     : https://prove2.me/submissions/dba276bb-f8bd-4cec-adc3-ae7e9de088a2

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_ordered_bounded_stops_future_increment_earlier_history_map
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (τ σ : Ω → ℝ≥0)
    (hstopτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (hstopσ : IsStoppingTime 𝓕 (fun ω => (σ ω : WithTop ℝ≥0)))
    (horder : ∀ ω, τ ω ≤ σ ω)
    (H : ℝ≥0) (hboundσ : ∀ ω, σ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hAτ : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    let QT : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))
    let QU : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))
    let Qτ : Measure Ω := P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (θ * X.X (τ ω) ω -
        (τ ω : ℝ) * X.ψ θ)))
    (∫⁻ ω in A,
      g (X.X (σ ω + u) ω - X.X (σ ω) ω) ∂QT) =
      Qτ A * (∫⁻ ω, g (X.X u ω) ∂QU) := by
  intro QT QU Qτ
  have hXu : Measurable (X.X u) := (X.adapted u).mono (𝓕.le u) le_rfl
  have hY : Measurable
      (fun ω => X.X (σ ω + u) ω - X.X (σ ω) ω) :=
    (measurable_pi_apply u).comp
      (levy_boundedStopping_stoppedFuturePath_measurable
        X σ hstopσ H hboundσ)
  have hLaw : Measure.map
      (fun ω => X.X (σ ω + u) ω - X.X (σ ω) ω)
        (QT.restrict A) =
      Qτ A • Measure.map (X.X u) QU :=
    esscher_ordered_bounded_stops_future_increment_earlier_history_map
      X θ hθ τ σ hstopτ hstopσ horder H hboundσ u T hT A hAτ
  have h1 := lintegral_map hg hY (μ := QT.restrict A)
  rw [← h1]
  rw [hLaw, lintegral_smul_measure, lintegral_map hg hXu, smul_eq_mul]
