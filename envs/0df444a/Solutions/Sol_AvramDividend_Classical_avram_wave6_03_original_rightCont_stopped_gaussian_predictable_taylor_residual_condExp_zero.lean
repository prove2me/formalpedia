-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:32:21.510963+00:00
-- url     : https://prove2.me/submissions/00ce8b90-5853-443c-b0cc-a7f64b6168f3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hG : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGI : Integrable (fun ω =>
      G ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) P)
    (hHI : Integrable H P)
    (hH2I : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let A : Ω → ℝ := fun ω => G ω * Y ω
    let R : Ω → ℝ := fun ω => H ω * Y ω ^ 2 - ((h : ℝ) * X.σ ^ 2) * H ω
    Integrable (A + R) P ∧
      P[A + R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  dsimp only
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  let A : Ω → ℝ := fun ω => G ω * Y ω
  let R : Ω → ℝ := fun ω =>
    H ω * Y ω ^ 2 - ((h : ℝ) * X.σ ^ 2) * H ω
  have hAI : Integrable A P := hGI
  have hRI : Integrable R P :=
    hH2I.sub (hHI.const_mul ((h : ℝ) * X.σ ^ 2))
  have hAZero :
      P[A | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) :=
    avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_zero
      X hν τ hτ B hbounded h G hG hGI
  have hRZero :
      P[R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero
      X hν τ hτ B hbounded h H hH hHI hH2I
  constructor
  · exact hAI.add hRI
  · calc
      P[A + R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
          =ᵐ[P]
        P[A | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] +
        P[R | (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] :=
          condExp_add hAI hRI _
      _ =ᵐ[P] (fun _ => (0 : ℝ)) := by
        filter_upwards [hAZero, hRZero] with ω ha hr
        calc
          _ = (0 : ℝ) + (0 : ℝ) := congrArg₂ (· + ·) ha hr
          _ = 0 := add_zero 0