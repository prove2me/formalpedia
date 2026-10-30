-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_predictable_cell_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:18:23.637165+00:00
-- url     : https://prove2.me/submissions/3f4eec65-200e-4dab-a407-c8bcb0eadf4b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- An adapted observation held over a future time cell is predictable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (s t : ℝ≥0) (f : Ω → ℝ)
    (hf : @Measurable Ω ℝ (𝓕 s) inferInstance f) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable inferInstance
      (fun p => if p.1 ∈ Set.Ioc s t then f p.2 else 0) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  intro B hB
  change MeasurableSet {p : ℝ≥0 × Ω |
    (if p.1 ∈ Set.Ioc s t then f p.2 else 0) ∈ B}
  have hpre : MeasurableSet (Set.Ioc s t ×ˢ {ω | f ω ∈ B}) :=
    measurableSet_predictable_Ioc_prod s t (hf hB)
  by_cases h0 : (0 : ℝ) ∈ B
  · have hcell : MeasurableSet (Set.Ioc s t ×ˢ (Set.univ : Set Ω)) :=
      measurableSet_predictable_Ioc_prod s t MeasurableSet.univ
    have heq : {p : ℝ≥0 × Ω |
        (if p.1 ∈ Set.Ioc s t then f p.2 else 0) ∈ B} =
        (Set.Ioc s t ×ˢ {ω | f ω ∈ B}) ∪
          (Set.Ioc s t ×ˢ (Set.univ : Set Ω))ᶜ := by
      ext p
      by_cases hp : s < p.1 ∧ p.1 ≤ t <;> simp [Set.mem_Ioc, hp, h0]
    rw [heq]
    exact hpre.union hcell.compl
  · have heq : {p : ℝ≥0 × Ω |
        (if p.1 ∈ Set.Ioc s t then f p.2 else 0) ∈ B} =
        Set.Ioc s t ×ˢ {ω | f ω ∈ B} := by
      ext p
      by_cases hp : s < p.1 ∧ p.1 ≤ t <;> simp [Set.mem_Ioc, hp, h0]
    rw [heq]
    exact hpre
