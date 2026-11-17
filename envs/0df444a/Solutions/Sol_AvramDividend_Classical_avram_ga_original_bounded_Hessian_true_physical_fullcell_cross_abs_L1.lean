-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_bounded_Hessian_true_physical_fullcell_cross_abs_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:02:10.028962+00:00
-- url     : https://prove2.me/submissions/57d2438d-d5c3-476f-85d0-15f1ba93f7b2

import Theorems.Thm_AvramDividend_Classical_avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
import Theorems.Thm_AvramDividend_Classical_avram_ga_masked_bounded_hessian_finite_sum_absolute_control
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
       (fun ω => (ρ ω : WithTop ℝ≥0)))
    (H : ℕ → ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m ω i, i < m → |H m i ω| ≤ K) :
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω ∧ s + Δ ≤ ρ ω
        then H m i ω / 2 * (R ^ 2 - Z ^ 2) else 0)
    (∀ m, Integrable (fun ω => |B m ω|) P) →
    Tendsto (fun m => ∫ ω, |B m ω| ∂P) atTop (nhds (0 : ℝ)) := by
  classical
  intro B hBI
  let Cross : ℕ → Ω → ℝ := fun m ω =>
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    ∑ i ∈ Finset.range m,
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : ℝ := X.X (s + Δ) ω - X.X s ω
      let Z : ℝ := R - (Δ : ℝ) * X.c
      if s < ρ ω ∧ s + Δ ≤ ρ ω then |R ^ 2 - Z ^ 2| else 0
  obtain ⟨hCI, hCLim⟩ :
      (∀ m, Integrable (Cross m) P) ∧
      Tendsto (fun m => ∫ ω, Cross m ω ∂P) atTop (nhds (0 : ℝ)) := by
    simpa only [Cross] using
      (avram_ga_a214_true_physical_fullcell_raw_centered_square_cross_expected_L1
        X hNuZero n ρ hρstop)
  have hBound (m : ℕ) (ω : Ω) : |B m ω| ≤ K / 2 * Cross m ω := by
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let cut : ℕ → Prop := fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      s < ρ ω ∧ s + Δ ≤ ρ ω
    let r : ℕ → ℝ := fun i =>
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : ℝ := X.X (s + Δ) ω - X.X s ω
      let Z : ℝ := R - (Δ : ℝ) * X.c
      R ^ 2 - Z ^ 2
    have hh : ∀ i ∈ Finset.range m, cut i → |H m i ω| ≤ K := by
      intro i hi hc
      exact hH m ω i (Finset.mem_range.mp hi)
    have h := avram_ga_masked_bounded_hessian_finite_sum_absolute_control
      (Finset.range m) cut (fun i => H m i ω) r K hK hh
    simpa only [B, Cross, cut, r, Δ] using h
  have hLower (m : ℕ) : 0 ≤ ∫ ω, |B m ω| ∂P :=
    integral_nonneg (fun ω => abs_nonneg _)
  have hUpper (m : ℕ) :
      (∫ ω, |B m ω| ∂P) ≤ K / 2 * (∫ ω, Cross m ω ∂P) := by
    calc
      _ ≤ ∫ ω, K / 2 * Cross m ω ∂P :=
        integral_mono_ae (hBI m) ((hCI m).const_mul _)
          (Filter.Eventually.of_forall (hBound m))
      _ = _ := integral_const_mul _ _
  have hScaled : Tendsto (fun m => K / 2 * (∫ ω, Cross m ω ∂P))
      atTop (nhds (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hCLim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hScaled hLower hUpper
