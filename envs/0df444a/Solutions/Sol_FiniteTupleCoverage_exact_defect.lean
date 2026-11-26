-- Prove2me | solution 1 for FiniteTupleCoverage.exact_defect
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T20:40:31.596418+00:00
-- url     : https://prove2.me/submissions/11940df9-bed8-4d48-8b41-2f57b5017e39

import Mathlib

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, DecidableEq (A i)] (allowed : ∀ i, Finset (A i))
    (listed : Finset (∀ i, A i)) :
    let seen := listed.filter (fun r => ∀ i, r i ∈ allowed i)
    ((Fintype.piFinset allowed) \ listed).card = (∏ i, (allowed i).card) - seen.card ∧
    (seen.card = (∏ i, (allowed i).card) ↔ ∀ r, (∀ i, r i ∈ allowed i) → r ∈ listed) := by
  intro seen
  let full := Fintype.piFinset allowed
  have members : ∀ r, r ∈ full ↔ ∀ i, r i ∈ allowed i :=
    fun _ => Fintype.mem_piFinset
  have intersect : full ∩ listed = seen := by
    ext r
    simp only [seen, Finset.mem_inter, Finset.mem_filter, members]
    exact and_comm
  have size : full.card = ∏ i, (allowed i).card := Fintype.card_piFinset allowed
  have total : (full \ listed).card + seen.card = full.card := by
    rw [← intersect]
    exact Finset.card_sdiff_add_card_inter _ _
  constructor
  · rw [← size]
    change (full \ listed).card = full.card - seen.card
    omega
  · rw [← size]
    have sub : seen ⊆ full := fun _ h => (members _).mpr (Finset.mem_filter.mp h).2
    constructor
    · intro same r legal
      have eq := Finset.eq_of_subset_of_card_le sub same.ge
      have incoming := (members r).mpr legal
      rw [← eq] at incoming
      exact (Finset.mem_filter.mp incoming).1
    · intro complete
      have eq : seen = full := by
        apply Finset.Subset.antisymm sub
        intro r hr
        have legal := (members r).mp hr
        exact Finset.mem_filter.mpr ⟨complete r legal,legal⟩
      rw [eq]

#print axioms solution
