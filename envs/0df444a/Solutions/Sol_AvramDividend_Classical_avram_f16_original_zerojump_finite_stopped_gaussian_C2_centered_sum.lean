-- Prove2me | solution 1 for AvramDividend.Classical.avram_f16_original_zerojump_finite_stopped_gaussian_C2_centered_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:25:47.513845+00:00
-- url     : https://prove2.me/submissions/069f7987-8612-41ea-87f5-126ea9b3aab2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_zerojump_stopped_C2_gaussian_bounded_ito_martingale
open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0)
    (KG KH : ι → ℝ)
    (hKG : ∀ i ∈ S, 0 ≤ KG i) (hKH : ∀ i ∈ S, 0 ≤ KH i) :
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
    (∀ i ∈ S, ∀ ω, |G i ω| ≤ KG i) →
    (∀ i ∈ S, ∀ ω, |H i ω| ≤ KH i) →
    let V : ι → Ω → ℝ := fun i ω =>
      X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
    Integrable (fun ω => Finset.sum S (fun i => G i ω * V i ω +
      (1 / 2 : ℝ) * (H i ω * ((V i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2)))) P ∧
    (∫ ω, Finset.sum S (fun i => G i ω * V i ω +
      (1 / 2 : ℝ) * (H i ω * ((V i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2))) ∂P) = 0 := by
  classical
  dsimp only
  intro hGB hHB
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
    X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c
  let Z : ι → Ω → ℝ := fun i ω => G i ω * V i ω +
    (1 / 2 : ℝ) * (H i ω * ((V i ω) ^ 2 - (h i : ℝ) * X.σ ^ 2))
  have hCell (i : ι) (hi : i ∈ S) :
      Integrable (Z i) P ∧ (∫ ω, Z i ω ∂P) = 0 := by
    have hc :=
      avram_wave7_05_turn6_original_zerojump_stopped_C2_gaussian_bounded_ito_martingale
        X hν x D hD w C hw q T (τ i) (hτ i hi)
        (B i) (hbounded i hi) (h i)
        (KG i) (KH i) (hKG i hi) (hKH i hi)
        (hGB i hi) (hHB i hi)
    dsimp only at hc
    simpa only [Z, G, H, V] using hc
  have hResult :
      Integrable (fun ω => Finset.sum S (fun i => Z i ω)) P ∧
      (∫ ω, Finset.sum S (fun i => Z i ω) ∂P) = 0 := by
    constructor
    · exact integrable_finset_sum S (fun i hi => (hCell i hi).1)
    · calc
        (∫ ω, Finset.sum S (fun i => Z i ω) ∂P) =
          ∑ i ∈ S, (∫ ω, Z i ω ∂P) :=
            integral_finset_sum S (fun i hi => (hCell i hi).1)
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          exact (hCell i hi).2
  exact hResult
