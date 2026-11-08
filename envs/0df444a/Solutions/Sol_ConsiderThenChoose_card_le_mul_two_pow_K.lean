-- Prove2me | solution 1 for ConsiderThenChoose.card_le_mul_two_pow_K
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T16:44:48.192715+00:00
-- url     : https://prove2.me/submissions/4a1b60c9-d6ba-4151-a8ea-004975a0a27b

import Mathlib
import Definitions.Def_ConsiderThenChoose_stateSpace

namespace Aux_CTC_card
open ConsiderThenChoose

lemma adj_ll {N K : ℕ} (C : Fin K → Finset (Fin N)) (i i' : Fin N) :
    ¬ (bipGraph C).Adj (Sum.inl i) (Sum.inl i') := by
  simp [bipGraph, SimpleGraph.fromRel_adj]

lemma adj_lr {N K : ℕ} (C : Fin K → Finset (Fin N)) (i : Fin N) (j : Fin K) :
    (bipGraph C).Adj (Sum.inl i) (Sum.inr j) ↔ i ∈ C j := by
  simp [bipGraph, SimpleGraph.fromRel_adj]

lemma adj_rl {N K : ℕ} (C : Fin K → Finset (Fin N)) (i : Fin N) (j : Fin K) :
    (bipGraph C).Adj (Sum.inr j) (Sum.inl i) ↔ i ∈ C j := by
  rw [SimpleGraph.adj_comm]; exact adj_lr C i j

lemma mem_vtx_l {N K : ℕ} (S : Finset (Fin N)) (T : Finset (Fin K)) (i : Fin N) :
    (Sum.inl i : Fin N ⊕ Fin K) ∈ vtx S T ↔ i ∈ S := by
  simp [vtx]

lemma mem_vtx_r {N K : ℕ} (S : Finset (Fin N)) (T : Finset (Fin K)) (j : Fin K) :
    (Sum.inr j : Fin N ⊕ Fin K) ∈ vtx S T ↔ j ∈ T := by
  simp [vtx]

lemma compA {N K : ℕ} (C : Fin K → Finset (Fin N)) {S0 S' : Finset (Fin N)}
    {T0 T' : Finset (Fin K)} (hc : IsComponent C S0 T0 S' T') (hT : T'.Nonempty)
    (i : Fin N) : i ∈ S' ↔ i ∈ S0 ∧ ∃ j ∈ T', i ∈ C j := by
  constructor
  · intro hi
    refine ⟨hc.1 hi, ?_⟩
    obtain ⟨j0, hj0⟩ := hT
    have hu : (Sum.inl i : Fin N ⊕ Fin K) ∈ vtx S' T' := (mem_vtx_l _ _ _).2 hi
    have hw : (Sum.inr j0 : Fin N ⊕ Fin K) ∈ vtx S' T' := (mem_vtx_r _ _ _).2 hj0
    haveI : Nontrivial (vtx S' T') :=
      nontrivial_of_ne (⟨_, hu⟩ : vtx S' T') ⟨_, hw⟩ (by simp)
    obtain ⟨⟨w, hwmem⟩, hadj⟩ :=
      hc.2.2.1.preconnected.exists_adj_of_nontrivial (⟨_, hu⟩ : vtx S' T')
    rw [SimpleGraph.induce_adj] at hadj
    rcases w with i' | j
    · exact absurd hadj (adj_ll C i i')
    · exact ⟨j, (mem_vtx_r _ _ _).1 hwmem, (adj_lr C i j).1 hadj⟩
  · rintro ⟨hi0, j, hj, hij⟩
    have h := hc.2.2.2 (Sum.inr j) ((mem_vtx_r _ _ _).2 hj) (Sum.inl i)
      ((mem_vtx_l _ _ _).2 hi0) ((adj_rl C i j).2 hij)
    exact (mem_vtx_l _ _ _).1 h

lemma invariant {N K : ℕ} (C : Fin K → Finset (Fin N)) (x : Finset (Fin N) × Finset (Fin K))
    (hx : InStateSpace C x) :
    x.1.Nonempty ∧ ∃ U : Set (Fin N), (∀ a ∈ U, ∀ b, a ≤ b → b ∈ U) ∧
      ∀ i, i ∈ x.1 ↔ i ∈ U ∧ ∃ j ∈ x.2, i ∈ C j := by
  induction hx with
  | root hc hS hT =>
    refine ⟨hS, Set.univ, fun _ _ _ _ => trivial, fun i => ?_⟩
    rw [compA C hc hT]
    simp
  | stock _ h hc hS hT ih =>
    obtain ⟨_, U, hU, hmem⟩ := ih
    refine ⟨hS, {i | Finset.min' _ h < i}, fun a ha b hab => lt_of_lt_of_le ha hab, fun i => ?_⟩
    rw [compA C hc hT]
    simp only [Finset.mem_erase, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hne, hiS⟩, hj⟩
      exact ⟨lt_of_le_of_ne (Finset.min'_le _ _ hiS) (Ne.symm hne), hj⟩
    · rintro ⟨hlt, j, hj, hij⟩
      have hmS := Finset.min'_mem _ h
      have hmU := ((hmem _).1 hmS).1
      have hTsub := hc.2.1
      refine ⟨⟨ne_of_gt hlt, (hmem i).2 ⟨hU _ hmU _ hlt.le, j, ?_, hij⟩⟩, j, hj, hij⟩
      exact (Finset.mem_sdiff.1 (hTsub hj)).1
  | skip _ h hc hS hT ih =>
    obtain ⟨_, U, hU, hmem⟩ := ih
    refine ⟨hS, {i | Finset.min' _ h < i}, fun a ha b hab => lt_of_lt_of_le ha hab, fun i => ?_⟩
    rw [compA C hc hT]
    simp only [Finset.mem_erase, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hne, hiS⟩, hj⟩
      exact ⟨lt_of_le_of_ne (Finset.min'_le _ _ hiS) (Ne.symm hne), hj⟩
    · rintro ⟨hlt, j, hj, hij⟩
      have hmS := Finset.min'_mem _ h
      have hmU := ((hmem _).1 hmS).1
      have hTsub := hc.2.1
      exact ⟨⟨ne_of_gt hlt, (hmem i).2 ⟨hU _ hmU _ hlt.le, j, hTsub hj, hij⟩⟩, j, hj, hij⟩

lemma determined {N K : ℕ} (C : Fin K → Finset (Fin N)) (x : Finset (Fin N) × Finset (Fin K))
    (hx : InStateSpace C x) (h : x.1.Nonempty) :
    ∀ i, i ∈ x.1 ↔ x.1.min' h ≤ i ∧ ∃ j ∈ x.2, i ∈ C j := by
  obtain ⟨_, U, hU, hmem⟩ := invariant C x hx
  intro i
  constructor
  · intro hi
    exact ⟨Finset.min'_le _ _ hi, ((hmem i).1 hi).2⟩
  · rintro ⟨hle, hj⟩
    have hmU := ((hmem _).1 (Finset.min'_mem _ h)).1
    exact (hmem i).2 ⟨hU _ hmU _ hle, hj⟩

end Aux_CTC_card

open ConsiderThenChoose Aux_CTC_card in
theorem solution {N K : ℕ} (C : Fin K → Finset (Fin N)) :
    (stateSpace C).ncard ≤ N * 2 ^ K := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have : stateSpace C = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨i, _⟩ := (invariant C x hx).1
      exact i.elim0
    rw [this]; simp
  · haveI : Inhabited (Fin N) := ⟨⟨0, hN⟩⟩
    classical
    let f : Finset (Fin N) × Finset (Fin K) → Fin N × Finset (Fin K) :=
      fun x => (if h : x.1.Nonempty then x.1.min' h else default, x.2)
    have hle := Set.ncard_le_ncard_of_injOn (s := stateSpace C) (t := Set.univ) f
      (fun _ _ => Set.mem_univ _) ?_
    · refine le_trans hle ?_
      rw [Set.ncard_univ, Nat.card_eq_fintype_card]
      simp
    · intro x hx y hy hxy
      have hx1 := (invariant C x hx).1
      have hy1 := (invariant C y hy).1
      simp only [f, dif_pos hx1, dif_pos hy1, Prod.mk.injEq] at hxy
      obtain ⟨hm, hT⟩ := hxy
      have hS : x.1 = y.1 := by
        ext i
        rw [determined C x hx hx1, determined C y hy hy1, hm, hT]
      exact Prod.ext hS hT
