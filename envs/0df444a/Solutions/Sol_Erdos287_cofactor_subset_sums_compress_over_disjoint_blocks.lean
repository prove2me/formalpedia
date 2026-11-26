-- Prove2me | solution 1 for Erdos287.cofactor_subset_sums_compress_over_disjoint_blocks
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:31:09.416624+00:00
-- url     : https://prove2.me/submissions/5c54df6e-f67f-43af-8478-b40819245924

import Mathlib

open Finset

set_option autoImplicit false

/-- Represent each subset sum by choosing one representative inside each
disjoint block and preserving the positions outside the blocks. -/
theorem solution (U I : Finset ℕ) (B : ℕ → Finset ℕ) (A : ℕ → Finset (Finset ℕ)) (w : ℕ → ℕ)
    (hpos : ∀ x ∈ U, 0 < w x)
    (hB : ∀ i ∈ I, B i ⊆ U)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (hA : ∀ i ∈ I, ∀ V ∈ A i, V ⊆ B i)
    (hlocal : ∀ i ∈ I, ∀ T ⊆ B i, ∃ V ∈ A i, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) :
    ∃ F : Finset (Finset ℕ),
      (∀ V ∈ F, V ⊆ U ∧ V.Nonempty) ∧
      (∀ T ⊆ U, T.Nonempty → ∃ V ∈ F, (∑ x ∈ V, w x) = ∑ x ∈ T, w x) ∧
      F.card ≤ 2 ^ (U \ I.biUnion B).card * ∏ i ∈ I, (A i).card := by
  classical
  let covered := I.biUnion B
  let F := U.powerset.filter (fun T => T.Nonempty ∧ ∀ i ∈ I, T ∩ B i ∈ A i)
  have hF (T : Finset ℕ) : T ∈ F ↔ T ⊆ U ∧ T.Nonempty ∧ ∀ i ∈ I, T ∩ B i ∈ A i := by
    simp [F]
  have hpair (V : ℕ → Finset ℕ) (hV : ∀ i ∈ I, V i ⊆ B i) :
      (↑I : Set ℕ).PairwiseDisjoint V :=
    fun i hi j hj hij => (hdisj i hi j hj hij).mono (hV i hi) (hV j hj)
  have hout (T : Finset ℕ) (V : ℕ → Finset ℕ) (hV : ∀ i ∈ I, V i ⊆ B i) :
      Disjoint (T \ covered) (I.biUnion V) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hy
    exact (mem_sdiff.mp hx).2 (mem_biUnion.mpr ⟨i, hi, hV i hi hxi⟩)
  have hrepresent (T : Finset ℕ) (hTU : T ⊆ U) (hTN : T.Nonempty) :
      ∃ R ∈ F, (∑ x ∈ R, w x) = ∑ x ∈ T, w x := by
    have hchoice (i : ℕ) (hi : i ∈ I) : ∃ V ∈ A i,
        (∑ x ∈ V, w x) = ∑ x ∈ T ∩ B i, w x :=
      hlocal i hi (T ∩ B i) inter_subset_right
    choose! V hVA hVsum using hchoice
    have hV (i : ℕ) (hi : i ∈ I) : V i ⊆ B i := hA i hi (V i) (hVA i hi)
    let R := (T \ covered) ∪ I.biUnion V
    have hRU : R ⊆ U := by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact hTU (mem_sdiff.mp hx).1
      · obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hx
        exact hB i hi (hV i hi hx)
    have hTpart : T = (T \ covered) ∪ I.biUnion (fun i => T ∩ B i) := by
      ext x
      constructor
      · intro hx
        by_cases hc : x ∈ covered
        · obtain ⟨i, hi, hxi⟩ := mem_biUnion.mp hc
          exact mem_union_right _ (mem_biUnion.mpr ⟨i, hi, mem_inter.mpr ⟨hx, hxi⟩⟩)
        · exact mem_union_left _ (mem_sdiff.mpr ⟨hx, hc⟩)
      · intro hx
        rcases mem_union.mp hx with hx | hx
        · exact (mem_sdiff.mp hx).1
        · obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hx
          exact (mem_inter.mp hx).1
    have hsum : (∑ x ∈ R, w x) = ∑ x ∈ T, w x := by
      calc
        (∑ x ∈ R, w x) = (∑ x ∈ T \ covered, w x) + ∑ i ∈ I, ∑ x ∈ V i, w x := by
          rw [show R = (T \ covered) ∪ I.biUnion V from rfl, sum_union (hout T V hV),
            sum_biUnion (hpair V hV)]
        _ = (∑ x ∈ T \ covered, w x) + ∑ i ∈ I, ∑ x ∈ T ∩ B i, w x := by
          rw [sum_congr rfl hVsum]
        _ = ∑ x ∈ T, w x := by
          rw [← sum_biUnion (hpair (fun i => T ∩ B i) (fun _ _ => inter_subset_right)),
            ← sum_union (hout T (fun i => T ∩ B i) (fun _ _ => inter_subset_right)), ← hTpart]
    have hRN : R.Nonempty := by
      obtain ⟨x, hx⟩ := hTN
      have hp := (hpos x (hTU hx)).trans_le (single_le_sum (f := w) (fun _ _ => Nat.zero_le _) hx)
      by_contra hn
      simp [not_nonempty_iff_eq_empty.mp hn] at hsum
      omega
    refine ⟨R, (hF R).mpr ⟨hRU, hRN, ?_⟩, hsum⟩
    intro i hi
    have hei : R ∩ B i = V i := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxR, hxB⟩ := mem_inter.mp hx
        rcases mem_union.mp hxR with hxout | hxvol
        · exact ((mem_sdiff.mp hxout).2 (mem_biUnion.mpr ⟨i, hi, hxB⟩)).elim
        · obtain ⟨j, hj, hxV⟩ := mem_biUnion.mp hxvol
          by_cases hij : i = j
          · exact hij.symm ▸ hxV
          · exact (disjoint_left.mp (hdisj i hi j hj hij) hxB (hV j hj hxV)).elim
      · intro hx
        exact mem_inter.mpr ⟨mem_union_right _ (mem_biUnion.mpr ⟨i, hi, hx⟩), hV i hi hx⟩
    exact hei.symm ▸ hVA i hi
  let encode (T : Finset ℕ) : Finset ℕ × (∀ i ∈ I, Finset ℕ) :=
    (T \ covered, fun i _ => T ∩ B i)
  have hmap : Set.MapsTo encode (↑F : Set (Finset ℕ))
      (↑((U \ covered).powerset ×ˢ I.pi A) : Set _) := by
    intro T hT
    obtain ⟨hTU, _, hTA⟩ := (hF T).mp hT
    refine mem_product.mpr ⟨mem_powerset.mpr ?_, mem_pi.mpr hTA⟩
    intro x hx
    obtain ⟨hxT, hxout⟩ := mem_sdiff.mp hx
    exact mem_sdiff.mpr ⟨hTU hxT, hxout⟩
  have hinj : Set.InjOn encode (↑F : Set (Finset ℕ)) := by
    intro T _ V _ he
    ext x
    by_cases hx : x ∈ covered
    · obtain ⟨i, hi, hx⟩ := mem_biUnion.mp hx
      have heq : T ∩ B i = V ∩ B i := congrArg (fun y => y.2 i hi) he
      simpa only [mem_inter, hx, and_true] using
        (show x ∈ T ∩ B i ↔ x ∈ V ∩ B i by rw [heq])
    · have heq : T \ covered = V \ covered := congrArg Prod.fst he
      simpa [hx] using (show x ∈ T \ covered ↔ x ∈ V \ covered by rw [heq])
  have hpi : (I.pi A).card = ∏ i ∈ I, (A i).card := Multiset.card_pi _ _
  refine ⟨F, fun T hT => ⟨((hF T).mp hT).1, ((hF T).mp hT).2.1⟩, hrepresent, ?_⟩
  calc
    F.card ≤ ((U \ covered).powerset ×ˢ I.pi A).card := card_le_card_of_injOn encode hmap hinj
    _ = _ := by rw [card_product, card_powerset, hpi]

