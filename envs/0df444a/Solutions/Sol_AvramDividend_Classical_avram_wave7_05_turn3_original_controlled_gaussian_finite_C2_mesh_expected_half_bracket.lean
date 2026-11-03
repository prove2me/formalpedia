-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn3_original_controlled_gaussian_finite_C2_mesh_expected_half_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:15:06.329202+00:00
-- url     : https://prove2.me/submissions/d8066303-3458-4d1f-9f07-2a7606552912

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_total_condExp_cell
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_discounted_ruin_controlled_gaussian_expected_taylor_cell

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
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B)
    (h : ι → ℝ≥0)
    (K₁ : ℝ) (hK₁ : 0 ≤ K₁)
    (hGbound : ∀ i ∈ S, ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) ω| ≤ K₁)
    (K₂ : ℝ) (hK₂ : 0 ≤ K₂)
    (hHbound : ∀ i ∈ S, ∀ ω : Ω, |(stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0))) ω| ≤ K₂) :
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
    (∀ i ∈ S, Integrable (fun ω =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2) P) ∧
    Integrable (fun ω => Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2)) P ∧
    (∫ ω, Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2) ∂P) =
      ∑ i ∈ S, (∫ ω,
        ((h i : ℝ) * X.σ ^ 2 / 2) * H i ω ∂P) := by
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
      Integrable (fun ω =>
        G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2) P ∧
      (∫ ω,
        G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2 ∂P) =
        (∫ ω, ((h i : ℝ) * X.σ ^ 2 / 2) * H i ω ∂P) := by
    intro i hi
    have hConditional :=
      avram_wave6_03_actual_discounted_ruin_stopped_controlled_C2_gaussian_total_condExp_cell
        X hν x D hD w C hw q T (τ i) (hτ i hi) B
        (hbounded i hi) (h i) K₁ hK₁ (hGbound i hi)
        K₂ hK₂ (hHbound i hi)
    have hExpected :=
      avram_wave7_05_original_discounted_ruin_controlled_gaussian_expected_taylor_cell
        X hν x D hD w C hw q T (τ i) (hτ i hi) B
        (hbounded i hi) (h i) K₁ hK₁ (hGbound i hi)
        K₂ hK₂ (hHbound i hi)
    dsimp only at hConditional hExpected
    exact ⟨hConditional.1, hExpected⟩
  have hAll : ∀ i ∈ S,
      Integrable (fun ω =>
        G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2) P := by
    intro i hi
    exact (hCells i hi).1
  have hSum : Integrable (fun ω => Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2)) P :=
    integrable_finset_sum S hAll
  change (∀ i ∈ S, Integrable (fun ω =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2) P) ∧
    Integrable (fun ω => Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2)) P ∧
    (∫ ω, Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2) ∂P) =
      ∑ i ∈ S, (∫ ω,
        ((h i : ℝ) * X.σ ^ 2 / 2) * H i ω ∂P)
  refine ⟨hAll, hSum, ?_⟩
  calc
    (∫ ω, Finset.sum S (fun i =>
      G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2) ∂P) =
        ∑ i ∈ S, (∫ ω,
          G i ω * Y i ω + (1 / 2 : ℝ) * H i ω * (Y i ω) ^ 2 ∂P) :=
          integral_finset_sum S hAll
    _ = ∑ i ∈ S, (∫ ω,
          ((h i : ℝ) * X.σ ^ 2 / 2) * H i ω ∂P) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (hCells i hi).2
