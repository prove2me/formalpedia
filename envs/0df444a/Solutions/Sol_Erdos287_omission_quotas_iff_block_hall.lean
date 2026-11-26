-- Prove2me | solution 1 for Erdos287.omission_quotas_iff_block_hall
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T13:33:31.777091+00:00
-- url     : https://prove2.me/submissions/5fddd9c4-7692-4ba4-ad29-df7fdee2a8de

import Mathlib

open Finset

set_option autoImplicit false

/-- When each run of candidate positions is a singleton or an adjacent pair,
joint omission quotas are exactly characterized by the Hall inequalities. -/
theorem solution (U P : Finset ℕ) (label block need : ℕ → ℕ)
    (hwithin : ∀ x ∈ U, ∀ y ∈ U, block x = block y →
      x = y ∨ x + 1 = y ∨ y + 1 = x)
    (hbetween : ∀ x ∈ U, x + 1 ∈ U → block x = block (x + 1)) :
    (∃ X ⊆ U, (∀ x ∈ X, x + 1 ∉ X) ∧
      ∀ p ∈ P, need p ≤ (X.filter (fun x => label x = p)).card) ↔
    ∀ S ⊆ P, (∑ p ∈ S, need p) ≤
      ((U.filter (fun x => label x ∈ S)).image block).card := by
  classical
  constructor
  · rintro ⟨X, hX, hsep, hneed⟩ S hS
    let A (p : ℕ) := X.filter (fun x => label x = p)
    let Z := X.filter (fun x => label x ∈ S)
    have hparts : S.biUnion A = Z := by
      ext x
      constructor
      · intro hx
        obtain ⟨p, hp, hx⟩ := mem_biUnion.mp hx
        obtain ⟨hx, he⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨hx, he.symm ▸ hp⟩
      · intro hx
        obtain ⟨hx, hp⟩ := mem_filter.mp hx
        exact mem_biUnion.mpr ⟨label x, hp, mem_filter.mpr ⟨hx, rfl⟩⟩
    have hdisj : (↑S : Set ℕ).PairwiseDisjoint A := by
      intro p hp q hq hpq
      exact disjoint_left.mpr fun x hx hy => hpq ((mem_filter.mp hx).2.symm.trans (mem_filter.mp hy).2)
    have hinj : Set.InjOn block (↑Z : Set ℕ) := by
      intro x hx y hy he
      have hxX := (mem_filter.mp hx).1
      have hyX := (mem_filter.mp hy).1
      rcases hwithin x (hX hxX) y (hX hyX) he with h | h | h
      · exact h
      · exact (hsep x hxX (h.symm ▸ hyX)).elim
      · exact (hsep y hyX (h.symm ▸ hxX)).elim
    calc
      _ ≤ ∑ p ∈ S, (A p).card := sum_le_sum fun p hp => hneed p (hS hp)
      _ = Z.card := by rw [← card_biUnion hdisj, hparts]
      _ = (Z.image block).card := (card_image_of_injOn hinj).symm
      _ ≤ _ := card_le_card (image_subset_image (fun x hx =>
        mem_filter.mpr ⟨hX (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩))
  · intro hcap
    let L := P.sigma (fun p => range (need p))
    let owner (j : ↥L) := j.val.1
    let N (p : ℕ) := (U.filter (fun x => label x = p)).image block
    let t (j : ↥L) := N (owner j)
    have hHall (S : Finset ↥L) : S.card ≤ (S.biUnion t).card := by
      let I := S.image owner
      have hI : I ⊆ P := by
        intro p hp
        obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
        exact (mem_sigma.mp j.property).1
      have hbound : S.card ≤ ∑ p ∈ I, need p := by
        have hmap : Set.MapsTo (fun j : ↥L => j.val) (↑S : Set ↥L)
            (↑(I.sigma (fun p => range (need p))) : Set (Σ _ : ℕ, ℕ)) := by
          intro j hj
          exact mem_sigma.mpr ⟨mem_image_of_mem owner hj, (mem_sigma.mp j.property).2⟩
        have hn := card_le_card_of_injOn (fun j : ↥L => j.val) hmap
          (fun _ _ _ _ e => Subtype.ext e)
        simpa [Finset.card_sigma] using hn
      have hblocks : (U.filter (fun x => label x ∈ I)).image block = S.biUnion t := by
        ext b
        constructor
        · intro hb
          obtain ⟨x, hx, rfl⟩ := mem_image.mp hb
          obtain ⟨hxU, hxI⟩ := mem_filter.mp hx
          obtain ⟨j, hjS, hlabel⟩ := mem_image.mp hxI
          exact mem_biUnion.mpr ⟨j, hjS, mem_image.mpr
            ⟨x, mem_filter.mpr ⟨hxU, hlabel.symm⟩, rfl⟩⟩
        · intro hb
          obtain ⟨j, hj, hb⟩ := mem_biUnion.mp hb
          obtain ⟨x, hx, hi⟩ := mem_image.mp hb
          obtain ⟨hxU, hxj⟩ := mem_filter.mp hx
          exact mem_image.mpr ⟨x, mem_filter.mpr
            ⟨hxU, hxj.symm ▸ mem_image_of_mem owner hj⟩, hi⟩
      rw [← hblocks]
      exact hbound.trans (hcap I hI)
    obtain ⟨f, hf, hft⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
    have hrep (j : ↥L) : ∃ x ∈ U, label x = owner j ∧ block x = f j := by
      obtain ⟨x, hx, he⟩ := mem_image.mp (hft j)
      exact ⟨x, (mem_filter.mp hx).1, (mem_filter.mp hx).2, he⟩
    choose pick hpU hpl hpb using hrep
    have hpInj : Function.Injective pick := fun j k he => hf (by rw [← hpb j, ← hpb k, he])
    let X := (univ : Finset ↥L).image pick
    have hX : X ⊆ U := by
      intro x hx
      obtain ⟨j, _, rfl⟩ := mem_image.mp hx
      exact hpU j
    refine ⟨X, hX, ?_, ?_⟩
    · intro x hx hsucc
      obtain ⟨j, _, hj⟩ := mem_image.mp hx
      obtain ⟨k, _, hk⟩ := mem_image.mp hsucc
      have he : f j = f k := by
        rw [← hpb j, ← hpb k, hj, hk]
        exact hbetween x (hX hx) (hX hsucc)
      rw [hf he, hk] at hj
      omega
    · intro p hp
      let token (i : Fin (need p)) : ↥L := ⟨⟨p, i.val⟩, mem_sigma.mpr ⟨hp, mem_range.mpr i.isLt⟩⟩
      let g (i : Fin (need p)) := pick (token i)
      have hmap : Set.MapsTo g (↑(univ : Finset (Fin (need p))) : Set (Fin (need p)))
          (↑(X.filter (fun x => label x = p)) : Set ℕ) := by
        intro i hi
        exact mem_filter.mpr ⟨mem_image_of_mem pick (mem_univ (token i)), hpl (token i)⟩
      have hinj : Set.InjOn g (↑(univ : Finset (Fin (need p))) : Set (Fin (need p))) := by
        intro i hi j hj he
        apply Fin.ext
        exact congrArg (fun k : ↥L => k.val.2) (hpInj he)
      simpa using card_le_card_of_injOn g hmap hinj

