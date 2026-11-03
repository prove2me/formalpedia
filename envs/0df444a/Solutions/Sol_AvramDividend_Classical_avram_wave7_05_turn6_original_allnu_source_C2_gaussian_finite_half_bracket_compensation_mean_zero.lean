-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_C2_gaussian_finite_half_bracket_compensation_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:25:55.507802+00:00
-- url     : https://prove2.me/submissions/e7fca0a1-c433-48f6-bc0c-abda82c0f40d

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn6_original_allnu_source_C2_gaussian_half_sigma_bracket_integral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-! Exact source C2 Gaussian Hessian quadratic compensation has zero mean
on any finite family of genuine original stopping times, with sigma squared/2. -/
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
    (h : ι → ℝ≥0) (H : ι → Ω → ℝ)
    (hHsource : ∀ i ∈ S, H i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          (let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
           if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (BH : ι → ℝ)
    (hBH : ∀ i ∈ S, 0 ≤ BH i)
    (hHbound : ∀ i ∈ S, ∀ ω, |H i ω| ≤ BH i) :
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
        (h i : ℝ) * Y.c
    let Q : ι → Ω → ℝ := fun i ω =>
      (1 / 2 : ℝ) * (((1 : ℝ) * V i ω) * (H i ω * V i ω)) -
        (((h i : ℝ) * X.σ ^ 2) / 2) * H i ω
    Integrable (fun ω => ∑ i ∈ S, Q i ω) P ∧
    (∫ ω, ∑ i ∈ S, Q i ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let V : ι → Ω → ℝ := fun i ω =>
    Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω -
      (h i : ℝ) * Y.c
  let Q : ι → Ω → ℝ := fun i ω =>
    (1 / 2 : ℝ) * (((1 : ℝ) * V i ω) * (H i ω * V i ω)) -
      (((h i : ℝ) * X.σ ^ 2) / 2) * H i ω
  have hCells : ∀ i ∈ S,
      Integrable (Q i) P ∧ (∫ ω, Q i ω ∂P) = 0 := by
    intro i hi
    have hPred :=
      avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
        X x D hD w C hw q T (τ i) (hτ i hi)
    dsimp only at hPred
    have hHG : Measurable (H i) := by
      rw [hHsource i hi]
      exact hPred.2.2.2
    have hHI : Integrable (H i) P := by
      apply Integrable.of_bound hHG.aestronglyMeasurable (BH i)
      exact Filter.Eventually.of_forall (fun ω => by
        simpa only [Real.norm_eq_abs] using hHbound i hi ω)
    have hOne :=
      avram_wave7_05_turn6_original_allnu_source_C2_gaussian_half_sigma_bracket_integral
        X Y hYν hYσ Jsmall Jlarge hSourceDecomp
        x D hD w C hw q T
        (τ i) (hτ i hi) (B i) (hbounded i hi)
        (h i) (H i) (hHsource i hi)
        (BH i) (hBH i hi) (hHbound i hi)
    dsimp only at hOne
    have hShift : Integrable
        (fun ω => (((h i : ℝ) * X.σ ^ 2) / 2) * H i ω) P :=
      hHI.const_mul _
    have hI : Integrable (Q i) P := hOne.1.sub hShift
    refine ⟨hI, ?_⟩
    change (∫ ω, (1 / 2 : ℝ) *
      (((1 : ℝ) * V i ω) * (H i ω * V i ω)) -
        (((h i : ℝ) * X.σ ^ 2) / 2) * H i ω ∂P) = 0
    rw [integral_sub hOne.1 hShift, hOne.2, integral_const_mul]
    ring
  have hAll : ∀ i ∈ S, Integrable (Q i) P :=
    fun i hi => (hCells i hi).1
  change Integrable (fun ω => ∑ i ∈ S, Q i ω) P ∧
    (∫ ω, ∑ i ∈ S, Q i ω ∂P) = 0
  refine ⟨integrable_finset_sum S hAll, ?_⟩
  calc
    (∫ ω, ∑ i ∈ S, Q i ω ∂P) =
        ∑ i ∈ S, (∫ ω, Q i ω ∂P) :=
      integral_finset_sum S hAll
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact (hCells i hi).2
