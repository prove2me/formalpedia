-- Prove2me | solution 1 for ConsiderThenChoose.min_eq_max_phi
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T18:39:45.867201+00:00
-- url     : https://prove2.me/submissions/936271b1-1410-4dcb-a2e2-b62e983ba5ec

import Mathlib
import Definitions.Def_ConsiderThenChoose_stateSpace
import Definitions.Def_ConsiderThenChoose_phi

namespace Aux_CTC_minphi
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

end Aux_CTC_minphi

open ConsiderThenChoose Aux_CTC_minphi in
theorem solution {N K : ℕ} (C : Fin K → Finset (Fin N))
    (x : Finset (Fin N) × Finset (Fin K)) (hx : x ∈ stateSpace C) :
    ∃ h : x.1.Nonempty, x.1.min' h ∈ phi C x ∧ ∀ p ∈ phi C x, p ≤ x.1.min' h := by
  have hx' : InStateSpace C x := hx
  have hne := (invariant C x hx').1
  refine ⟨hne, ?_, ?_⟩
  · unfold phi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun q hq => Finset.min'_le _ _ hq, ?_⟩
    exact ((determined C x hx' hne _).1 (Finset.min'_mem _ hne)).2
  · intro p hp
    unfold phi at hp
    rw [Finset.mem_filter] at hp
    exact hp.2.1 _ (Finset.min'_mem _ hne)
