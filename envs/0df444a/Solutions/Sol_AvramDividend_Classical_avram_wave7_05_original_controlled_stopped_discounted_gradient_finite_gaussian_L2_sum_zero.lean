-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_controlled_stopped_discounted_gradient_finite_gaussian_L2_sum_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:57:30.639258+00:00
-- url     : https://prove2.me/submissions/fb289ace-6f6e-4cd8-bc26-abd809fbf0a8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (S : Finset ι) (h : ι → ℝ≥0) (K : ℝ) (hK : 0 ≤ K)
    (hHbound : ∀ ω : Ω, |(stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))) ω| ≤ K) :
    let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
    let F : ι → Ω → ℝ := fun i ω =>
      H ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω -
        (h i : ℝ) * X.c)
    (∀ i ∈ S, MemLp (F i) 2 P) ∧
      MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
      Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by
  classical
  let H : Ω → ℝ := stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            deriv w (Function.leftLim
              (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))
  let F : ι → Ω → ℝ := fun i ω =>
    H ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω -
      (h i : ℝ) * X.c)
  have hPoint :
      ∀ i ∈ S,
        MemLp (F i) 2 P ∧
        Integrable (F i) P ∧
          (∫ ω, F i ω ∂P) = 0 := by
    intro i hi
    have hOne :=
      avram_wave7_05_original_controlled_stopped_discounted_gradient_gaussian_L2_mean_zero
        X hν x D hD w q T τ hτ B hbounded (h i) K hK hHbound
    dsimp only at hOne
    simpa only [F, H] using hOne
  have hLpAll : ∀ i ∈ S, MemLp (F i) 2 P := by
    intro i hi
    exact (hPoint i hi).1
  have hIntAll : ∀ i ∈ S, Integrable (F i) P := by
    intro i hi
    exact (hPoint i hi).2.1
  have hSumLp : MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P :=
    memLp_finset_sum S hLpAll
  have hSumI : Integrable (fun ω => ∑ i ∈ S, F i ω) P :=
    integrable_finset_sum S hIntAll
  change (∀ i ∈ S, MemLp (F i) 2 P) ∧
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0
  refine ⟨hLpAll, hSumLp, hSumI, ?_⟩
  calc
    (∫ ω, ∑ i ∈ S, F i ω ∂P) =
      ∑ i ∈ S, ∫ ω, F i ω ∂P :=
      integral_finset_sum S hIntAll
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact (hPoint i hi).2.2
