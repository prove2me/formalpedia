-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_jump12_initial_event_masked_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T15:13:30.018336+00:00
-- url     : https://prove2.me/submissions/874d3085-c2b5-442d-8e78-43a5d2af1a20

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => ((A.indicator σ ω : ℝ≥0) : WithTop ℝ≥0)) := by
  classical
  intro t
  have h0t : (0 : ℝ≥0) ≤ t := zero_le
  have hA_t : MeasurableSet[𝓕.rightCont t] A :=
    (𝓕.rightCont.mono h0t A) hA
  have hEvent :
      {ω : Ω | ((A.indicator σ ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        Aᶜ ∪ (A ∩ {ω : Ω | (σ ω : WithTop ℝ≥0) ≤ t}) := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω, hω]
    · have h0le : ((0 : ℝ≥0) : WithTop ℝ≥0) ≤
          (t : WithTop ℝ≥0) :=
        WithTop.coe_le_coe.mpr (zero_le : (0 : ℝ≥0) ≤ t)
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.indicator_of_notMem hω]
      constructor
      · intro _
        exact Or.inl hω
      · intro _
        exact h0le
  rw [hEvent]
  exact hA_t.compl.union (hA_t.inter (hσ t))
