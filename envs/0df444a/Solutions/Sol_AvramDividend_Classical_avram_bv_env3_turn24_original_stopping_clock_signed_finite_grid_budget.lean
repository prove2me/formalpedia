-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn24_original_stopping_clock_signed_finite_grid_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:10:37.415548+00:00
-- url     : https://prove2.me/submissions/ef9928ce-3627-405d-bcb9-405f63d9556d

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn27_original_stopping_clock_condexp_selected_cell_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Finite stopped original martingale plus HJB drift via selected-cell zero mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (m : ℕ)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range m,
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0)
      ∂P) ≤ 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hA (i : ℕ) :
      MeasurableSet {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} :=
    (𝓕.rightCont).le (u i) _
      (avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
        X τ hStop u i)
  have hMaskI (i : ℕ) (f : Ω → ℝ) (hf : Integrable f P) :
      Integrable (fun ω => if (u i : WithTop ℝ≥0) < τ ω then f ω else 0) P := by
    have hEq : (fun ω : Ω =>
        if (u i : WithTop ℝ≥0) < τ ω then f ω else 0) =
        {ω : Ω | (u i : WithTop ℝ≥0) < τ ω}.indicator f := by
      funext ω
      by_cases h : (u i : WithTop ℝ≥0) < τ ω
      · simpa only [Set.indicator_apply, Set.mem_setOf_eq, if_pos h]
      · simpa only [Set.indicator_apply, Set.mem_setOf_eq, if_neg h]
    rw [hEq]
    exact hf.indicator (hA i)
  have hI (i : ℕ) : Integrable (fun ω : Ω =>
      if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) P :=
    hMaskI i (fun ω => M i ω + B i ω) ((hMI i).add (hBI i))
  have hBound (i : ℕ) : (∫ ω,
      if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0 ∂P) ≤ 0 := by
    have hLe (ω : Ω) :
        (if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) ≤
        (if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) := by
      by_cases h : (u i : WithTop ℝ≥0) < τ ω
      · simp only [if_pos h]; linarith [hDrift i ω]
      · simp only [if_neg h, le_rfl]
    calc
      (∫ ω, if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0 ∂P) ≤
        (∫ ω, if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0 ∂P) :=
        integral_mono_ae (hI i) (hMaskI i (M i) (hMI i))
          (Filter.Eventually.of_forall hLe)
      _ = 0 := avram_bv_env3_turn27_original_stopping_clock_condexp_selected_cell_mean_zero
        X τ hStop u M hMI hCondZero i
  constructor
  · exact integrable_finset_sum _ (by intro i hi; exact hI i)
  · rw [integral_finset_sum (Finset.range m) (by
      intro i hi
      exact hI i)]
    exact Finset.sum_nonpos (fun i hi => hBound i)
