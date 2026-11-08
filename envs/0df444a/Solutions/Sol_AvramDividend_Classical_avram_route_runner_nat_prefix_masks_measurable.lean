-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_nat_prefix_masks_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:26:23.702425+00:00
-- url     : https://prove2.me/submissions/f9967812-eba6-4ed7-92ce-382b7ea53b7a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (k : Ω → ℕ)
    (hPrefix : ∀ i : ℕ, MeasurableSet {ω : Ω | i < k ω}) :
    Measurable k := by
  classical
  have hFiber (i : ℕ) : MeasurableSet {ω : Ω | k ω = i} := by
    cases i with
    | zero =>
      have heq : {ω : Ω | k ω = 0} = {ω : Ω | ¬ 0 < k ω} := by
        ext ω
        simp only [Set.mem_setOf_eq]
        omega
      rw [heq]
      exact (hPrefix 0).compl
    | succ n =>
      have heq :
          {ω : Ω | k ω = n + 1} =
          {ω : Ω | n < k ω} ∩ {ω : Ω | ¬ n + 1 < k ω} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        omega
      rw [heq]
      exact (hPrefix n).inter (hPrefix (n + 1)).compl
  intro s _
  have heq : k ⁻¹' s = ⋃ i ∈ s, {ω : Ω | k ω = i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro h
      exact ⟨k ω, h, rfl⟩
    · rintro ⟨i, hi, hki⟩
      simpa [hki] using hi
  rw [heq]
  exact MeasurableSet.biUnion (Set.to_countable s) (fun i _ => hFiber i)
