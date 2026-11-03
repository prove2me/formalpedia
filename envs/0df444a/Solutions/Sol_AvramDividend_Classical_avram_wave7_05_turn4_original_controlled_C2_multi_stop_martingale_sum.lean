-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn4_original_controlled_C2_multi_stop_martingale_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:29:25.572385+00:00
-- url     : https://prove2.me/submissions/1cc35268-7269-4d81-966a-7938f6dfe9e8

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_controlled_C2_gaussian_one_cell_centered_martingale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B)
    (h : ι → ℝ≥0)
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ i ∈ S, ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) ω| ≤ K)
    (hHI : ∀ i ∈ S, Integrable (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) P)
    (hWeightedI : ∀ i ∈ S, Integrable (fun ω =>
      (stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) ω *
        (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
          (h i : ℝ) * X.c) ^ 2) P) :
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
    let Y : ι → Ω → ℝ := fun i ω =>
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
    Integrable (fun ω => Finset.sum S (fun i =>
      G i ω * Y i ω +
        (1 / 2 : ℝ) * (H i ω * ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2)))) P ∧
    (∫ ω, Finset.sum S (fun i =>
      G i ω * Y i ω +
        (1 / 2 : ℝ) * (H i ω * ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2))) ∂P) =
      0 := by
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
  let Y : ι → Ω → ℝ := fun i ω =>
    X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
  have hCells : ∀ i ∈ S,
      Integrable (fun ω => G i ω * Y i ω +
        (1 / 2 : ℝ) * (H i ω * ((Y i ω) ^ 2 -
          (h i : ℝ) * X.σ ^ 2))) P ∧
      (∫ ω, G i ω * Y i ω +
        (1 / 2 : ℝ) * (H i ω * ((Y i ω) ^ 2 -
          (h i : ℝ) * X.σ ^ 2)) ∂P) = 0 := by
    intro i hi
    have hOne :=
      avram_wave7_05_turn3_original_controlled_C2_gaussian_one_cell_centered_martingale
        X hν x D hD w C hw q T (τ i) (hτ i hi) B (hbounded i hi)
        (h i) K hK (hGbound i hi) (hHI i hi) (hWeightedI i hi)
    dsimp only at hOne
    exact hOne
  have hAll : ∀ i ∈ S,
      Integrable (fun ω => G i ω * Y i ω +
        (1 / 2 : ℝ) * (H i ω * ((Y i ω) ^ 2 -
          (h i : ℝ) * X.σ ^ 2))) P := by
    intro i hi
    exact (hCells i hi).1
  have hSum : Integrable (fun ω => Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * (H i ω *
        ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2)))) P :=
    integrable_finset_sum S hAll
  change Integrable (fun ω => Finset.sum S (fun i =>
    G i ω * Y i ω + (1 / 2 : ℝ) * (H i ω *
      ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2)))) P ∧
    (∫ ω, Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * (H i ω *
        ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2))) ∂P) = 0
  refine ⟨hSum, ?_⟩
  calc
    (∫ ω, Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * (H i ω *
        ((Y i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2))) ∂P) =
        ∑ i ∈ S, (∫ ω, G i ω * Y i ω +
          (1 / 2 : ℝ) * (H i ω * ((Y i ω) ^ 2 -
            (h i : ℝ) * X.σ ^ 2)) ∂P) :=
          integral_finset_sum S hAll
    _ = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact (hCells i hi).2
