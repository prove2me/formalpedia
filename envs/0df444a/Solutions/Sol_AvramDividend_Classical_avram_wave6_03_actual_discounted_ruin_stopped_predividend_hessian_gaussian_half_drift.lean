-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_actual_discounted_ruin_stopped_predividend_hessian_gaussian_half_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T00:03:30.711194+00:00
-- url     : https://prove2.me/submissions/2228adc8-1dac-47c4-ad51-35f9c1996531

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Exact discounted stopped original pre-dividend second-order Ito coefficient. -/
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
    (h : ℝ≥0) (H : Ω → ℝ)
    (hHdef : H = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ ω : WithTop ℝ≥0)))
    (hHI : Integrable H P)
    (hWeightedInt : Integrable (fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    Integrable (fun ω => (1 / 2 : ℝ) * H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P ∧
    (∫ ω, (1 / 2 : ℝ) * H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2 ∂P) =
      ((h : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H ω ∂P) := by
  classical
  subst H
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
  let a : ℝ := (h : ℝ) * X.σ ^ 2
  have hWeightedI : Integrable (fun ω => H ω * Y ω ^ 2) P := hWeightedInt
  have hHI' : Integrable H P := hHI
  have hRes :=
    avram_wave6_03_actual_discounted_ruin_stopped_hessian_gaussian_quadratic_compensator_zero
      X hν x D hD w C hw q T τ hτ B hbounded h hHI hWeightedInt
  have hZero : (∫ ω, H ω * (Y ω ^ 2 - a) ∂P) = 0 := hRes.2
  have hMulI : Integrable (fun ω => H ω * a) P := hHI'.mul_const a
  have hEq : (fun ω => H ω * (Y ω ^ 2 - a)) =
      (fun ω => H ω * Y ω ^ 2 - H ω * a) := by
    funext ω
    ring
  rw [hEq, integral_sub hWeightedI hMulI, integral_mul_const] at hZero
  have hBalance : (∫ ω, H ω * Y ω ^ 2 ∂P) =
      (∫ ω, H ω ∂P) * a :=
    sub_eq_zero.mp hZero
  have hFun : (fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) =
      (fun ω => (1 / 2 : ℝ) * (H ω * Y ω ^ 2)) := by
    funext ω
    ring
  change Integrable (fun ω => (1 / 2 : ℝ) * H ω * Y ω ^ 2) P ∧
    (∫ ω, (1 / 2 : ℝ) * H ω * Y ω ^ 2 ∂P) =
      ((h : ℝ) * X.σ ^ 2 / 2) * (∫ ω, H ω ∂P)
  rw [hFun]
  constructor
  · exact hWeightedI.const_mul (1 / 2 : ℝ)
  · rw [integral_const_mul, hBalance]
    dsimp [a]
    ring
