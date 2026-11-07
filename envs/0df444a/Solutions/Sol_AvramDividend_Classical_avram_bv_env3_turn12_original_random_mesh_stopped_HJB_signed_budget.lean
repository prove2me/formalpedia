-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn12_original_random_mesh_stopped_HJB_signed_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:32:20.866061+00:00
-- url     : https://prove2.me/submissions/862bf431-46ed-4c51-8cd7-8d3c84aad64a

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuinely stopped random original mesh has nonpositive signed source
whenever its centered martingale prefix has zero mean and HJB cells are nonpositive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hDrift : ∀ i ω, B i ω ≤ 0)
    (hMMean : (∫ ω, ∑ i ∈ Finset.range (k ω),
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) ∂P) = 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) ∂P) ≤ 0 := by
  classical
  let S : ℕ → Set Ω :=
    fun i => {ω : Ω | (u i : WithTop ℝ≥0) < τ ω}
  have hm (i : ℕ) : MeasurableSet (S i) :=
    (𝓕.rightCont).le (u i) _
      (avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
        X τ hStop u i)
  have hMaskI (i : ℕ) (f : Ω → ℝ) (hf : Integrable f P) :
      Integrable (fun ω => if (u i : WithTop ℝ≥0) < τ ω then f ω else 0) P := by
    have heq : (fun ω : Ω => if (u i : WithTop ℝ≥0) < τ ω then f ω else 0) =
        (S i).indicator f := by
      funext ω
      by_cases h : (u i : WithTop ℝ≥0) < τ ω
      · have hs : ω ∈ S i := h
        simp only [if_pos h, Set.indicator_of_mem hs]
      · have hs : ω ∉ S i := h
        simp only [if_neg h, Set.indicator_of_notMem hs]
    rw [heq]
    exact hf.indicator (hm i)
  have hM : Integrable (fun ω : Ω => ∑ i ∈ Finset.range (k ω),
      if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) P :=
    avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
      P m k hk hkBound _ (fun i => hMaskI i (M i) (hMI i))
  have hPlus : Integrable (fun ω : Ω => ∑ i ∈ Finset.range (k ω),
      if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) P :=
    avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
      P m k hk hkBound _ (fun i => hMaskI i
        (fun ω => M i ω + B i ω) ((hMI i).add (hBI i)))
  have hLe (ω : Ω) :
      (∑ i ∈ Finset.range (k ω),
        if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) ≤
      (∑ i ∈ Finset.range (k ω),
        if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : (u i : WithTop ℝ≥0) < τ ω
    · simp only [if_pos h]
      linarith [hDrift i ω]
    · simp only [if_neg h, le_rfl]
  constructor
  · exact hPlus
  · calc
      (∫ ω, ∑ i ∈ Finset.range (k ω),
        (if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) ∂P) ≤
          (∫ ω, ∑ i ∈ Finset.range (k ω),
            (if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) ∂P) :=
        integral_mono_ae hPlus hM (Filter.Eventually.of_forall hLe)
      _ = 0 := hMMean
