-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn6_original_allnu_source_gaussian_multistop_gradient_automatic_L2_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:13:23.590462+00:00
-- url     : https://prove2.me/submissions/377adedd-a2c2-45de-9087-9a19435f8f82

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
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
Bounded original-reserve stopped derivatives are automatically stopping-time
measurable; every same-filtration Gaussian source increment is L² centred.
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
    (B : ι → ℝ≥0)
    (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun t ω =>
      if t ≤ T then
        (Real.exp (-(q * (t : ℝ))) *
          deriv w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
        (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun ω => (τ i ω : WithTop ℝ≥0)))
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K i) :
    let V : ι → Ω → ℝ := fun i ω =>
      Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
    let F : ι → Ω → ℝ := fun i ω => G i ω * V i ω
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by
  classical
  let V : ι → Ω → ℝ := fun i ω =>
    Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
  let F : ι → Ω → ℝ := fun i ω => G i ω * V i ω
  have hCell : ∀ i ∈ S,
      Integrable (F i) P ∧ (∫ ω, F i ω ∂P) = 0 := by
    intro i hi
    have hPred :=
      avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
        X x D hD w C hw q T (τ i) (hτ i hi)
    dsimp only at hPred
    have hStop :
        Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace]
          (G i) := by
      rw [hGsource i hi]
      exact hPred.1
    have hGlobal : Measurable (G i) := by
      rw [hGsource i hi]
      exact hPred.2.2.1
    have hOne :=
      avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
        Y hYν (τ i) (hτ i hi) (B i) (hbounded i hi)
        (h i) (G i) hStop hGlobal
        (K i) (hK i hi) (hGbound i hi)
    dsimp only at hOne
    exact ⟨hOne.2.1, hOne.2.2⟩
  change Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0
  have hCellsInt : ∀ i ∈ S, Integrable (F i) P :=
    fun i hi => (hCell i hi).1
  refine ⟨integrable_finset_sum S hCellsInt, ?_⟩
  calc
    (∫ ω, ∑ i ∈ S, F i ω ∂P) =
        ∑ i ∈ S, (∫ ω, F i ω ∂P) :=
      integral_finset_sum S hCellsInt
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact (hCell i hi).2
