-- Prove2me | solution 1 for AvramDividend.Classical.avram_route_runner_nat_prefix_all_preimages_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:58:04.426194+00:00
-- url     : https://prove2.me/submissions/7d1c69c4-a9c1-45de-bc87-21ed2b17cbaf

import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section

/-- Countably many strict-threshold events determine a natural-valued selector. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (k : Ω → ℕ)
    (hPrefix : ∀ i : ℕ, MeasurableSet {ω : Ω | i < k ω}) :
    ∀ s : Set ℕ, MeasurableSet (k ⁻¹' s) := by
  classical
  have hfib : ∀ n : ℕ, MeasurableSet {ω : Ω | k ω = n} := by
    intro n
    cases n with
    | zero =>
      have heq : {ω : Ω | k ω = 0} =
          ({ω : Ω | 0 < k ω} : Set Ω)ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
        omega
      rw [heq]
      exact (hPrefix 0).compl
    | succ n =>
      have heq : {ω : Ω | k ω = n + 1} =
          {ω : Ω | n < k ω} \ {ω : Ω | n + 1 < k ω} := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_diff]
        omega
      rw [heq]
      exact (hPrefix n).diff (hPrefix (n + 1))
  intro s
  have heq : k ⁻¹' s =
      ⋃ n : ℕ, if n ∈ s then {ω : Ω | k ω = n} else ∅ := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion]
    constructor
    · intro h
      refine ⟨k ω, ?_⟩
      simp [h]
    · rintro ⟨n, h⟩
      split_ifs at h with hn
      · simp only [Set.mem_setOf_eq] at h
        simpa [h] using hn
      · simp at h
  rw [heq]
  exact MeasurableSet.iUnion (fun n => by
    split_ifs with hn
    · exact hfib n
    · exact MeasurableSet.empty)
