-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn5_original_allnu_sameX_controlled_C2_half_bracket_mesh_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:05:16.147774+00:00
-- url     : https://prove2.me/submissions/47185707-f918-4a45-b2c3-da90227573d3

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-!
Canonical controlled original-source Gaussian C² half-bracket mesh mean zero.
The coefficient is exactly the clipped source Hessian with factor one half.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) :
    let G : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
    (∀ i ∈ S, Integrable (fun ω => G i ω * V i ω) P) →
    (∀ i ∈ S, Integrable (fun ω => (1 / 2 : ℝ) * H i ω) P) →
    (∀ i ∈ S, Integrable (fun ω =>
      ((1 / 2 : ℝ) * H i ω) * (V i ω) ^ 2) P) →
    Integrable (fun ω => Finset.sum S (fun i => G i ω * V i ω + (1 / 2 : ℝ) * H i ω * (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) P ∧
    (∫ ω, Finset.sum S (fun i => G i ω * V i ω + (1 / 2 : ℝ) * H i ω * (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) ∂P) = 0 := by
  classical
  let G : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
    if t ≤ T then
      (Real.exp (-(q * (t : ℝ))) *
        deriv w (Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
      (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
  let H : ι → Ω → ℝ := fun i => stoppedValue (fun t ω =>
    if t ≤ T then
      (Real.exp (-(q * (t : ℝ))) *
        (let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
         if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
      (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
    else 0) (fun ω => (τ i ω : WithTop ℝ≥0))
  let V : ι → Ω → ℝ := fun i ω =>
    Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
  dsimp only
  intro hGI hHI hH2I
  let HH : ι → Ω → ℝ := fun i ω => (1 / 2 : ℝ) * H i ω
  have hGS : ∀ i ∈ S, G i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)) := by
    intro i hi
    rfl
  have hHS : ∀ i ∈ S, HH i = fun ω => (1 / 2 : ℝ) * (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) ω := by
    intro i hi
    rfl
  have hMean :=
    avram_wave7_05_turn5_original_allnu_sameX_gaussian_residual_C2_finite_mesh_mean_zero
      X Y hYν hYσ Jsmall Jlarge hSourceDecomp
      x D hD w C hw q T S τ hτ B hbounded h G HH
      hGS hHS hGI hHI hH2I
  dsimp only at hMean
  have hEq : (fun ω => Finset.sum S (fun i => G i ω * V i ω + (1 / 2 : ℝ) * H i ω * (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) =
      (fun ω => Finset.sum S (fun i => G i ω * V i ω + (HH i ω * V i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * HH i ω))) := by
    funext ω
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [HH]
    ring
  change Integrable (fun ω => Finset.sum S (fun i => G i ω * V i ω + (1 / 2 : ℝ) * H i ω * (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2))) P ∧
    (∫ ω, Finset.sum S (fun i => G i ω * V i ω + (1 / 2 : ℝ) * H i ω * (V i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) ∂P) = 0
  rw [hEq]
  exact hMean
