-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_turn4_original_allnu_multi_stop_C2_gaussian_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:11:57.814475+00:00
-- url     : https://prove2.me/submissions/986af975-3fed-4b39-ae97-8dca04fd2e28

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0) (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s}) :
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
    (∀ (i : ι) (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (G i) ∧
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (H i)) ∧
    Measurable (fun ω => ∑ i ∈ S, G i ω) ∧
    Measurable (fun ω => ∑ i ∈ S, H i ω) ∧
    Measurable (fun ω => Finset.sum S (fun i => (G i ω) ^ 2 + (H i ω) ^ 2)) := by
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
  have hCells : ∀ (i : ι) (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (G i) ∧
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (H i) ∧
      Measurable (G i) ∧ Measurable (H i) := by
    intro i hi
    have hOne :=
      avram_wave7_05_turn3_original_allnu_stopped_controlled_gradient_hessian_joint_predictable
        X x D hD w C hw q T (τ i) (hτ i hi)
    dsimp only at hOne
    exact hOne
  change (∀ (i : ι) (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (G i) ∧
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (H i)) ∧
    Measurable (fun ω => ∑ i ∈ S, G i ω) ∧
    Measurable (fun ω => ∑ i ∈ S, H i ω) ∧
    Measurable (fun ω => Finset.sum S (fun i => (G i ω) ^ 2 + (H i ω) ^ 2))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨(hCells i hi).1, (hCells i hi).2.1⟩
  · exact Finset.measurable_sum S (fun i hi => (hCells i hi).2.2.1)
  · exact Finset.measurable_sum S (fun i hi => (hCells i hi).2.2.2)
  · apply Finset.measurable_sum
    intro i hi
    have hEq : (G i * G i + H i * H i) =
        (fun ω : Ω => (G i ω) ^ 2 + (H i ω) ^ 2) := by
      funext ω
      simp [pow_two, Pi.add_apply, Pi.mul_apply]
    rw [← hEq]
    exact (((hCells i hi).2.2.1.mul (hCells i hi).2.2.1).add
      ((hCells i hi).2.2.2.mul (hCells i hi).2.2.2))
