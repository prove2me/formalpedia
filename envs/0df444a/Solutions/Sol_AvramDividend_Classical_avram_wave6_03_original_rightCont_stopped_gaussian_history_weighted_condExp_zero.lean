-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:54:52.169254+00:00
-- url     : https://prove2.me/submissions/e3b66850-639b-41ed-8a67-2ba924e83293

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Source Gaussian stopped-history predictable tests have conditional mean zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P) :
    P[(fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hMom :=
    avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
      X hν τ hτ B hbounded h
  change Integrable Y P ∧
    (P[Y | hτstop.measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable (fun ω => Y ω ^ 2) P ∧
    (P[(fun ω => Y ω ^ 2) | hτstop.measurableSpace]
      =ᵐ[P] (fun _ => (h : ℝ) * X.σ ^ 2)) at hMom
  have hHI : Integrable (H * Y) P := hProdI
  have hPull : P[H * Y | hτstop.measurableSpace] =ᵐ[P]
      H * P[Y | hτstop.measurableSpace] :=
    condExp_mul_of_stronglyMeasurable_left
      hH.stronglyMeasurable hHI hMom.1
  change P[H * Y | hτstop.measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ))
  filter_upwards [hPull, hMom.2.1] with ω hp hz
  calc
    (P[H * Y | hτstop.measurableSpace]) ω =
        (H * P[Y | hτstop.measurableSpace]) ω := hp
    _ = H ω * (P[Y | hτstop.measurableSpace]) ω := rfl
    _ = 0 := by rw [hz]; ring
