-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_discounted_ruin_controlled_gaussian_expected_taylor_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:46:32.192604+00:00
-- url     : https://prove2.me/submissions/2af5ebed-94fd-4812-ab40-afdcb573a1cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_total_condExp_cell

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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hGbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K₁)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K₂) :
    let G : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let H : Ω → ℝ := stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    (∫ ω, G ω * Y ω + (1 / 2 : ℝ) * H ω * Y ω ^ 2 ∂P) =
      ∫ ω, ((h : ℝ) * X.σ ^ 2 / 2) * H ω ∂P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let G : Ω → ℝ := stoppedValue (fun t ω =>
    if t ≤ T then
      (Real.exp (-(q * (t : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
      (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let H : Ω → ℝ := stoppedValue (fun t ω =>
    if t ≤ T then
      (Real.exp (-(q * (t : ℝ))) *
        (let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
         if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
      (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hCell :=
    avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_total_condExp_cell
      X hν x D hD w C hw q T τ hτ B hbounded h
      K₁ hK₁ hGbound K₂ hK₂ hHbound
  dsimp only at hCell
  have hCE : P[(fun ω => G ω * Y ω + (1 / 2 : ℝ) * H ω * Y ω ^ 2) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] =ᵐ[P]
      (fun ω => ((h : ℝ) * X.σ ^ 2 / 2) * H ω) := hCell.2
  have hIntegralEq :
      (∫ ω, (P[(fun ω => G ω * Y ω + (1 / 2 : ℝ) * H ω * Y ω ^ 2) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P) =
      (∫ ω, G ω * Y ω + (1 / 2 : ℝ) * H ω * Y ω ^ 2 ∂P) :=
    integral_condExp (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace_le
  change (∫ ω, G ω * Y ω + (1 / 2 : ℝ) * H ω * Y ω ^ 2 ∂P) =
    ∫ ω, ((h : ℝ) * X.σ ^ 2 / 2) * H ω ∂P
  calc
    (∫ ω, G ω * Y ω + (1 / 2 : ℝ) * H ω * Y ω ^ 2 ∂P) =
        ∫ ω, (P[(fun ω => G ω * Y ω + (1 / 2 : ℝ) * H ω * Y ω ^ 2) |
          (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P :=
      hIntegralEq.symm
    _ = ∫ ω, ((h : ℝ) * X.σ ^ 2 / 2) * H ω ∂P :=
      integral_congr_ae hCE
