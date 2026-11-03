-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_C2_gaussian_one_cell_centered_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:48:30.723758+00:00
-- url     : https://prove2.me/submissions/e2de61dd-4d28-49e7-833f-67d72c8ef731

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
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
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K)
    (hHI : Integrable (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) P)
    (hWeightedI : Integrable (fun ω =>
      (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω *
        (X.X (τ ω + h) ω - X.X (τ ω) ω -
          (h : ℝ) * X.c) ^ 2) P) :
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
    Integrable (fun ω => G ω * Y ω +
      (1 / 2 : ℝ) * (H ω * ((Y ω) ^ 2 - (h : ℝ) * X.σ ^ 2))) P ∧
    (∫ ω, G ω * Y ω +
      (1 / 2 : ℝ) * (H ω * ((Y ω) ^ 2 - (h : ℝ) * X.σ ^ 2)) ∂P) = 0 := by
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
  have hGrad :=
    avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
      X hν x D hD w q T τ hτ B hbounded h K hK hGbound
  dsimp only at hGrad
  have hHess :=
    avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero
      X hν x D hD w C hw q T τ hτ B hbounded h hHI hWeightedI
  dsimp only at hHess
  have hSecond : Integrable (fun ω =>
      (1 / 2 : ℝ) * (H ω * ((Y ω) ^ 2 -
        (h : ℝ) * X.σ ^ 2))) P :=
    hHess.1.const_mul _
  have hCellI : Integrable (fun ω => G ω * Y ω +
      (1 / 2 : ℝ) * (H ω * ((Y ω) ^ 2 -
        (h : ℝ) * X.σ ^ 2))) P :=
    hGrad.2.1.add hSecond
  change Integrable (fun ω => G ω * Y ω +
      (1 / 2 : ℝ) * (H ω * ((Y ω) ^ 2 -
        (h : ℝ) * X.σ ^ 2))) P ∧
    (∫ ω, G ω * Y ω +
      (1 / 2 : ℝ) * (H ω * ((Y ω) ^ 2 -
        (h : ℝ) * X.σ ^ 2)) ∂P) = 0
  refine ⟨hCellI, ?_⟩
  rw [integral_add hGrad.2.1 hSecond, integral_const_mul,
    hGrad.2.2, hHess.2]
  ring
