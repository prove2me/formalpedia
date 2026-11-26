-- Prove2me | solution 1 for Erdos287.cofactor_subset_sums_compress_over_disjoint_additive_triples
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:23:04.593727+00:00
-- url     : https://prove2.me/submissions/4e81584e-cef4-42d1-a21d-78f265b91910

import Mathlib

open Finset

set_option autoImplicit false

/-- A disjoint triple with one additive relation needs seven local patterns
to represent every subset sum. -/
theorem solution (U I : Finset ℕ) (a b c w : ℕ → ℕ)
    (hblocks : ∀ i ∈ I, ({a i, b i, c i} : Finset ℕ) ⊆ U)
    (hne : ∀ i ∈ I, a i ≠ b i ∧ a i ≠ c i ∧ b i ≠ c i)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint ({a i, b i, c i} : Finset ℕ) {a j, b j, c j})
    (hweight : ∀ i ∈ I, w (a i) = w (b i) + w (c i)) :
    ∃ F : Finset (Finset ℕ),
      (∀ V ∈ F, V ⊆ U ∧ V.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) ∧
      F.card ≤ 7 ^ I.card * 2 ^ (U.card - 3 * I.card) := by
  classical
  let block (i : ℕ) : Finset ℕ := {a i, b i, c i}
  let banned (i : ℕ) : Finset ℕ := {b i, c i}
  let covered := I.biUnion block
  let allowed (i : ℕ) := (block i).powerset.erase (banned i)
  let canonical (T : Finset ℕ) := ∀ i ∈ I, T ∩ block i ≠ banned i
  let F := U.powerset.filter (fun T => T.Nonempty ∧ canonical T)
  have hF (T : Finset ℕ) : T ∈ F ↔ T ⊆ U ∧ T.Nonempty ∧ canonical T := by
    simp [F]
  have hrepr (n : ℕ) : ∀ T ⊆ U, T.Nonempty → T.card = n →
      ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro T hTU hT hn
      by_cases ht : canonical T
      · exact ⟨T, (hF T).mpr ⟨hTU, hT, ht⟩, rfl⟩
      change ¬ ∀ i ∈ I, T ∩ block i ≠ banned i at ht
      push Not at ht
      obtain ⟨i, hi, he⟩ := ht
      obtain ⟨hab, hac, hbc⟩ := hne i hi
      have hb : b i ∈ T := (mem_inter.mp (he.symm ▸ (show b i ∈ banned i by simp [banned]))).1
      have hc : c i ∈ T := (mem_inter.mp (he.symm ▸ (show c i ∈ banned i by simp [banned]))).1
      have ha : a i ∉ T := by
        intro h
        have hm : a i ∈ T ∩ block i := mem_inter.mpr ⟨h, by simp [block]⟩
        rw [he] at hm
        simpa [banned, hab, hac] using hm
      let R := (T.erase (b i)).erase (c i)
      let V := insert (a i) R
      have haR : a i ∉ R := by simp [R, ha]
      have hc' : c i ∈ T.erase (b i) := mem_erase.mpr ⟨hbc.symm, hc⟩
      have hRU : R ⊆ U := ((erase_subset _ _).trans (erase_subset _ _)).trans hTU
      have hVU : V ⊆ U := insert_subset (hblocks i hi (by simp)) hRU
      have hVR : V.card < n := by
        rw [← hn]
        simp only [V, R, card_insert_of_notMem haR, card_erase_of_mem hc', card_erase_of_mem hb]
        have : 0 < (T.erase (b i)).card := card_pos.mpr ⟨_, hc'⟩
        rw [card_erase_of_mem hb] at this
        omega
      have hsum : (∑ x ∈ V, w x) = ∑ x ∈ T, w x := by
        have h₁ := sum_erase_add T w hb
        have h₂ := sum_erase_add (T.erase (b i)) w hc'
        change (∑ x ∈ insert (a i) R, w x) = _
        rw [sum_insert haR, hweight i hi]
        change (∑ x ∈ R, w x) + w (c i) = _ at h₂
        omega
      obtain ⟨A, hAF, heq⟩ := ih V.card hVR V hVU (by simp [V]) rfl
      exact ⟨A, hAF, heq.trans hsum⟩
  let encode (T : Finset ℕ) : Finset ℕ × (∀ i ∈ I, Finset ℕ) :=
    (T \ covered, fun i _ => T ∩ block i)
  have hmap : Set.MapsTo encode (↑F : Set (Finset ℕ))
      (↑((U \ covered).powerset ×ˢ I.pi allowed) : Set _) := by
    intro T hT
    obtain ⟨hTU, _, hTcan⟩ := (hF T).mp hT
    refine mem_product.mpr ⟨mem_powerset.mpr ?_, mem_pi.mpr ?_⟩
    · intro x hx
      obtain ⟨hxT, hxout⟩ := mem_sdiff.mp hx
      exact mem_sdiff.mpr ⟨hTU hxT, hxout⟩
    · intro i hi
      exact mem_erase.mpr ⟨hTcan i hi, mem_powerset.mpr inter_subset_right⟩
  have hinj : Set.InjOn encode (↑F : Set (Finset ℕ)) := by
    intro T _ V _ he
    ext x
    by_cases hx : x ∈ covered
    · obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hx
      have heq : T ∩ block i = V ∩ block i := congrArg (fun y => y.2 i hi) he
      simpa only [mem_inter, hx, and_true] using
        (show x ∈ T ∩ block i ↔ x ∈ V ∩ block i by rw [heq])
    · have heq : T \ covered = V \ covered := congrArg Prod.fst he
      simpa [hx] using (show x ∈ T \ covered ↔ x ∈ V \ covered by rw [heq])
  have hsub : covered ⊆ U := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hx
    exact hblocks i hi hxi
  have hcard (i : ℕ) (hi : i ∈ I) : (block i).card = 3 := by
    obtain ⟨hab, hac, hbc⟩ := hne i hi
    simp [block, card_insert_of_notMem, hab, hac, hbc]
  have hcovered : covered.card = 3 * I.card := by
    rw [card_biUnion (show (↑I : Set ℕ).PairwiseDisjoint block from
      fun i hi j hj hij => hdisj i hi j hj hij)]
    rw [sum_congr rfl hcard]
    simp [mul_comm]
  have hlocal (i : ℕ) (hi : i ∈ I) : (allowed i).card = 7 := by
    have hm : banned i ∈ (block i).powerset := mem_powerset.mpr (by simp [banned, block])
    rw [show (allowed i).card = ((block i).powerset.erase (banned i)).card from rfl,
      card_erase_of_mem hm, card_powerset, hcard i hi]
    decide
  have hpi : (I.pi allowed).card = ∏ i ∈ I, (allowed i).card := Multiset.card_pi _ _
  refine ⟨F, fun T hT => ⟨((hF T).mp hT).1, ((hF T).mp hT).2.1⟩,
    fun T hTU hT => hrepr T.card T hTU hT rfl, ?_⟩
  calc
    F.card ≤ ((U \ covered).powerset ×ˢ I.pi allowed).card := card_le_card_of_injOn encode hmap hinj
    _ = 7 ^ I.card * 2 ^ (U.card - 3 * I.card) := by
      rw [card_product, card_powerset, card_sdiff_of_subset hsub, hcovered, hpi]
      rw [prod_congr rfl hlocal]
      simp [mul_comm]

