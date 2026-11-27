-- Prove2me | solution 1 for Erdos287.cofactor_split_pattern_count
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:41:16.096013+00:00
-- url     : https://prove2.me/submissions/0eb75bea-c935-4529-a953-824ed75658ae

import Mathlib

open Finset

set_option autoImplicit false

/-- Count admissible cofactor patterns with a fixed selected endpoint and
one or more selected cofactors from each disjoint split block. -/
theorem solution (U I : Finset ℕ) (c : ℕ) (A : ℕ → Finset ℕ) (hc : c ∈ U)
    (hA : ∀ i ∈ I, A i ⊆ U.erase c)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (A i) (A j)) :
    let F := U.powerset.filter (fun T => c ∈ T ∧ ∀ i ∈ I, (T ∩ A i).Nonempty)
    F.card ≤ 2 ^ (U.card - (1 + ∑ i ∈ I, (A i).card)) *
      ∏ i ∈ I, (2 ^ (A i).card - 1) := by
  classical
  intro F
  let blocks := I.biUnion A
  let covered := insert c blocks
  let allowed (i : ℕ) := (A i).powerset.erase ∅
  let encode (T : Finset ℕ) : Finset ℕ × (∀ i ∈ I, Finset ℕ) :=
    (T \ covered, fun i _ => T ∩ A i)
  have hz (T : Finset ℕ) : T ∈ F ↔ T ⊆ U ∧ c ∈ T ∧ ∀ i ∈ I, (T ∩ A i).Nonempty := by
    simp only [F, mem_filter, mem_powerset]
  have hmap : Set.MapsTo encode (↑F : Set (Finset ℕ))
      (↑((U \ covered).powerset ×ˢ I.pi allowed) : Set _) := by
    intro T hT
    obtain ⟨hTU, _, hit⟩ := (hz T).mp hT
    refine mem_product.mpr ⟨mem_powerset.mpr ?_, mem_pi.mpr ?_⟩
    · intro x hx
      obtain ⟨hxT, hxout⟩ := mem_sdiff.mp hx
      exact mem_sdiff.mpr ⟨hTU hxT, hxout⟩
    · intro i hi
      exact mem_erase.mpr ⟨(hit i hi).ne_empty, mem_powerset.mpr inter_subset_right⟩
  have hinj : Set.InjOn encode (↑F : Set (Finset ℕ)) := by
    intro T hT V hV he
    ext x
    by_cases hxc : x = c
    · subst x
      exact iff_of_true ((hz T).mp hT).2.1 ((hz V).mp hV).2.1
    · by_cases hx : x ∈ blocks
      · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
        have heq : T ∩ A i = V ∩ A i := congrArg (fun y => y.2 i hi) he
        simpa only [mem_inter, hxi, and_true] using
          (show x ∈ T ∩ A i ↔ x ∈ V ∩ A i by rw [heq])
      · have hxout : x ∉ covered := by simp [covered, hxc, hx]
        have heq : T \ covered = V \ covered := congrArg Prod.fst he
        simpa [hxout] using (show x ∈ T \ covered ↔ x ∈ V \ covered by rw [heq])
  have blockSub : blocks ⊆ U.erase c := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
    exact hA i hi hxi
  have hcOut : c ∉ blocks := fun h => (notMem_erase c U) (blockSub h)
  have hsub : covered ⊆ U := insert_subset hc (blockSub.trans (erase_subset _ _))
  have hsize : covered.card = 1 + ∑ i ∈ I, (A i).card := by
    change (insert c blocks).card = _
    rw [card_insert_of_notMem hcOut, show blocks.card = _ from
      card_biUnion (show (↑I : Set ℕ).PairwiseDisjoint A from
        fun i hi j hj hij => hdisj i hi j hj hij), add_comm]
  have hpatt (i : ℕ) (hi : i ∈ I) : (allowed i).card = 2 ^ (A i).card - 1 := by
    change ((A i).powerset.erase ∅).card = _
    rw [card_erase_of_mem (mem_powerset.mpr (empty_subset _)), card_powerset]
  have hpi : (I.pi allowed).card = ∏ i ∈ I, (allowed i).card := Multiset.card_pi _ _
  calc
    F.card ≤ ((U \ covered).powerset ×ˢ I.pi allowed).card := card_le_card_of_injOn encode hmap hinj
    _ = 2 ^ (U.card - (1 + ∑ i ∈ I, (A i).card)) * ∏ i ∈ I, (2 ^ (A i).card - 1) := by
      rw [card_product, card_powerset, card_sdiff_of_subset hsub, hsize, hpi, prod_congr rfl hpatt]

