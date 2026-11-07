-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn12_original_double_stopped_condexp_random_mesh_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:28:11.270286+00:00
-- url     : https://prove2.me/submissions/4fd5d44a-6f4f-4a20-a3cd-440425dd1835

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A bounded stopping index adapted at the physical mesh's left edges
preserves centering of the original Lévy source increments under both cuts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (hkAdapt : ∀ i,
      MeasurableSet[𝓕.rightCont (u i)] {ω : Ω | i < k ω})
    (M : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let f : ℕ → Ω → ℝ := fun i ω => if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0
  have hm (i : ℕ) : MeasurableSet {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} :=
    (𝓕.rightCont).le (u i) _
      (avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
        X τ hStop u i)
  have hf (i : ℕ) : Integrable (f i) P := by
    have heq : f i = {ω : Ω | (u i : WithTop ℝ≥0) < τ ω}.indicator (M i) := by
      funext ω
      by_cases h : (u i : WithTop ℝ≥0) < τ ω
      · have hs : ω ∈ {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} := h
        simp only [f, if_pos h, Set.indicator_of_mem hs]
      · have hs : ω ∉ {ω : Ω | (u i : WithTop ℝ≥0) < τ ω} := h
        simp only [f, if_neg h, Set.indicator_of_notMem hs]
    rw [heq]
    exact (hMI i).indicator (hm i)
  have hMean (i : ℕ) (_hi : i < m) :
      (∫ ω, if i < k ω then f i ω else 0 ∂P) = 0 := by
    let S : Set Ω := {ω : Ω | i < k ω ∧ (u i : WithTop ℝ≥0) < τ ω}
    have hPred : MeasurableSet[𝓕.rightCont (u i)] S :=
      (hkAdapt i).inter
        (avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
          X τ hStop u i)
    have hMeas : MeasurableSet S := (𝓕.rightCont).le (u i) _ hPred
    have hCondRestrict : ∀ᵐ ω ∂P.restrict S,
        condExp (𝓕.rightCont (u i)) P (M i) ω = 0 :=
      ae_restrict_of_ae (hCondZero i)
    have hSetIntegral :=
      setIntegral_condExp ((𝓕.rightCont).le (u i)) (hMI i) hPred
    have hZero : (∫ ω in S, M i ω ∂P) = 0 := by
      calc
        (∫ ω in S, M i ω ∂P) =
            (∫ ω in S, condExp (𝓕.rightCont (u i)) P (M i) ω ∂P) :=
          hSetIntegral.symm
        _ = 0 := by
          rw [integral_congr_ae hCondRestrict]
          simp
    have hMask : (fun ω : Ω => if i < k ω then f i ω else 0) = S.indicator (M i) := by
      funext ω
      by_cases ha : i < k ω
      · by_cases hb : (u i : WithTop ℝ≥0) < τ ω
        · have hs : ω ∈ S := ⟨ha, hb⟩
          simp only [f, if_pos ha, if_pos hb, Set.indicator_of_mem hs]
        · have hs : ω ∉ S := fun hh => hb hh.2
          simp only [f, if_pos ha, if_neg hb, Set.indicator_of_notMem hs]
      · have hs : ω ∉ S := fun hh => ha hh.1
        simp only [if_neg ha, Set.indicator_of_notMem hs]
    rw [hMask, integral_indicator hMeas]
    exact hZero
  constructor
  · exact avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
      P m k hk hkBound f hf
  · exact avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
      P m k hk hkBound f hf hMean
