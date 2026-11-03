-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_finite_multistop_curvature_covariance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:13:59.298903+00:00
-- url     : https://prove2.me/submissions/d615962b-7f44-4051-b292-046632700740

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_curvature_covariance
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Original arbitrary-nu controlled stopped C2 Gaussian finite-mesh covariance,
with the exact sum of sigma-squared per-cell quadratic variation coefficients. -/
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
    (B : ι → ℝ≥0)
    (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (hHsource : ∀ i ∈ S, H i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (BG BH : ι → ℝ)
    (hBG : ∀ i ∈ S, 0 ≤ BG i) (hBH : ∀ i ∈ S, 0 ≤ BH i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ BG i)
    (hHbound : ∀ i ∈ S, ∀ ω, |H i ω| ≤ BH i) :
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
        (h i : ℝ) * Y.c
    let F : ι → Ω → ℝ := fun i ω =>
      (G i ω * V i ω) * (H i ω * V i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) =
      ∑ i ∈ S, ((h i : ℝ) * X.σ ^ 2) *
        (∫ ω, G i ω * H i ω ∂P) := by
  classical
  let V : ι → Ω → ℝ := fun i ω =>
    Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
      (h i : ℝ) * Y.c
  let F : ι → Ω → ℝ := fun i ω =>
    (G i ω * V i ω) * (H i ω * V i ω)
  have hCell : ∀ i ∈ S,
      Integrable (F i) P ∧
        (∫ ω, F i ω ∂P) =
          ((h i : ℝ) * X.σ ^ 2) *
            (∫ ω, G i ω * H i ω ∂P) := by
    intro i hi
    have hOne :=
      avram_wave7_05_turn6_original_allnu_source_C2_gaussian_bounded_curvature_covariance
        X Y hYν hYσ Jsmall Jlarge hSourceDecomp
        x D hD w C hw q T
        (τ i) (hτ i hi) (B i) (hbounded i hi)
        (h i) (G i) (H i) (hGsource i hi) (hHsource i hi)
        (BG i) (BH i) (hBG i hi) (hBH i hi)
        (hGbound i hi) (hHbound i hi)
    dsimp only at hOne
    exact hOne
  have hCellI : ∀ i ∈ S, Integrable (F i) P :=
    fun i hi => (hCell i hi).1
  change Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) =
      ∑ i ∈ S, ((h i : ℝ) * X.σ ^ 2) *
        (∫ ω, G i ω * H i ω ∂P)
  refine ⟨integrable_finset_sum S hCellI, ?_⟩
  calc
    (∫ ω, ∑ i ∈ S, F i ω ∂P) =
        ∑ i ∈ S, (∫ ω, F i ω ∂P) :=
      integral_finset_sum S hCellI
    _ = ∑ i ∈ S, ((h i : ℝ) * X.σ ^ 2) *
          (∫ ω, G i ω * H i ω ∂P) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hCell i hi).2
