-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_true_clock_marked_horizon_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:31:33.915197+00:00
-- url     : https://prove2.me/submissions/e9e1892e-0516-4f39-b565-0e0e5eca5a22

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original right-continuous predictable marked clock measures its actual horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} (T : ℝ≥0) :
    MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))]
      {p : ((ℝ≥0 × Ω) × ℝ) | p.1.1 ≤ T} := by
  have h0 : MeasurableSet[𝓕.rightCont.predictable]
      (({0} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_singleton_bot_prod
      (𝓕 := 𝓕.rightCont) MeasurableSet.univ
  have hIoc : MeasurableSet[𝓕.rightCont.predictable]
      (Ioc 0 T ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictable_Ioc_prod
      (𝓕 := 𝓕.rightCont) 0 T MeasurableSet.univ
  have hshape : {p : ℝ≥0 × Ω | p.1 ≤ T} =
      (({0} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω)) ∪
        (Ioc 0 T ×ˢ Set.univ) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, and_true, Set.mem_Ioc]
    constructor
    · intro ht
      rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ p.1) with heq | hpos
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hpos, ht⟩
    · rintro (heq | ⟨_, ht⟩)
      · simpa [heq] using (zero_le T)
      · exact ht
  have hbase : MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω | p.1 ≤ T} := by
    rw [hshape]
    exact h0.union hIoc
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  exact hbase.preimage measurable_fst
