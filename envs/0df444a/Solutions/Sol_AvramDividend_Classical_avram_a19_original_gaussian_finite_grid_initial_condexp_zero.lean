-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_original_gaussian_finite_grid_initial_condexp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T00:21:30.598911+00:00
-- url     : https://prove2.me/submissions/d1883d3f-5e92-4848-9db6-cd15898ee51d

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory

/-- Original finite stopped Gaussian grid gains remain centred conditionally on the initial filtration. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (m₀ : MeasurableSpace Ω) {ι : Type*}
    (s : Finset ι) (G : ι → Ω → ℝ)
    (hInt : ∀ i ∈ s, Integrable (G i) P)
    (hCond : ∀ i ∈ s,
      condExp m₀ P (G i) =ᵐ[P] (fun _ => (0 : ℝ))) :
    Integrable (fun ω => ∑ i ∈ s, G i ω) P ∧
    condExp m₀ P (fun ω => ∑ i ∈ s, G i ω)
      =ᵐ[P] (fun _ => (0 : ℝ))  := by
  refine ⟨integrable_finset_sum s hInt, ?_⟩
  have hAll : ∀ᵐ ω ∂P, ∀ i ∈ s,
      condExp m₀ P (G i) ω = 0 := by
    exact (Filter.eventually_all_finset s).2 hCond
  have hSum := condExp_finset_sum (s := s) hInt m₀
  have hFn : (∑ i ∈ s, G i) =
      (fun ω => ∑ i ∈ s, G i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  have hCEFn : (∑ i ∈ s, condExp m₀ P (G i)) =
      (fun ω => ∑ i ∈ s, condExp m₀ P (G i) ω) := by
    funext ω
    simp only [Finset.sum_apply]
  have hEq : condExp m₀ P (fun ω => ∑ i ∈ s, G i ω) =ᵐ[P]
      (fun ω => ∑ i ∈ s, condExp m₀ P (G i) ω) := by
    rw [hFn, hCEFn] at hSum
    exact hSum
  filter_upwards [hEq, hAll] with ω hEqω hZero
  rw [hEqω]
  apply Finset.sum_eq_zero
  intro i hi
  exact hZero i hi
