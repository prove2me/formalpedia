-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_past_count_atom_history_comap_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:53:31.8944+00:00
-- url     : https://prove2.me/submissions/3999c4d5-83bf-4267-9339-ff05b053aad6

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- A finite past count cylinder is measurable in the pulled-back count path sigma-algebra. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (N : Ω → ℝ → ℕ) (clock : ℝ)
    (n : ℕ) (a b : Fin n → Set.Iic clock)
    (j : Fin n) (v : Fin n → ℕ) :
    MeasurableSet[
      MeasurableSpace.comap
        (fun ω : Ω => fun s : Set.Iic clock => N ω (s : ℝ))
        (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))]
      {ω | ∀ i : Fin n, i < j →
        N ω (b i : ℝ) - N ω (a i : ℝ) = v i} := by
  have hEach : ∀ i : Fin n, MeasurableSet
      {p : Set.Iic clock → ℕ |
        i < j → p (b i) - p (a i) = v i} := by
    intro i
    by_cases hij : i < j
    · simp only [hij, true_implies]
      measurability
    · simp [hij]
  have hC : MeasurableSet
      {p : Set.Iic clock → ℕ |
        ∀ i : Fin n, i < j → p (b i) - p (a i) = v i} := by
    simpa only [Set.setOf_forall] using (MeasurableSet.iInter hEach)
  exact (MeasurableSpace.measurableSet_comap).2 ⟨_, hC, rfl⟩
