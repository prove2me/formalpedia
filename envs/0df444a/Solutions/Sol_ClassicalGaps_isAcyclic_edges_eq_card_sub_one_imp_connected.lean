-- Prove2me | solution 1 for ClassicalGaps.isAcyclic_edges_eq_card_sub_one_imp_connected
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-24T22:25:26.369075+00:00
-- url     : https://prove2.me/submissions/75191682-05b6-4c8f-9e5b-de121aae51ea

import Mathlib

open SimpleGraph

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.IsAcyclic) (hcard : Nat.card G.edgeSet + 1 = Nat.card V) :
    G.Connected := by
  classical
  have hVne : Nonempty V := by
    have h1 : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
    rw [h1] at hcard
    have : Fintype.card V ≠ 0 := by omega
    exact Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero this)
  have hne : (Finset.univ.filter (fun H : SimpleGraph V => H.IsAcyclic)).Nonempty :=
    ⟨⊥, by simp⟩
  obtain ⟨F, hF_mem, hF_max⟩ :=
    Finset.exists_max_image (Finset.univ.filter (fun H : SimpleGraph V => H.IsAcyclic))
      (fun H => Nat.card H.edgeSet) hne
  have hF_acyc : F.IsAcyclic := (Finset.mem_filter.mp hF_mem).2
  have hF_conn : F.Connected := by
    haveI := hVne
    refine ⟨fun u v => ?_⟩
    by_contra hnr
    have hacyc' : (F ⊔ edge u v).IsAcyclic := hF_acyc.sup_edge_of_not_reachable hnr
    have hmem' : F ⊔ edge u v ∈ Finset.univ.filter (fun H : SimpleGraph V => H.IsAcyclic) := by
      simp [hacyc']
    have hle := hF_max (F ⊔ edge u v) hmem'
    have huv : u ≠ v := fun h => hnr (h ▸ Reachable.refl _)
    have hlt : Nat.card F.edgeSet < Nat.card (F ⊔ edge u v).edgeSet := by
      have hsub : F.edgeSet ⊂ (F ⊔ edge u v).edgeSet := by
        rw [Set.ssubset_iff_of_subset (edgeSet_mono le_sup_left)]
        exact ⟨s(u, v), by simp [huv], by
          intro hmem
          exact absurd (Adj.reachable hmem) hnr⟩
      exact Set.ncard_lt_ncard hsub (Set.toFinite _)
    omega
  have hF_tree : F.IsTree := ⟨hF_conn, hF_acyc⟩
  have hF_card : Nat.card F.edgeSet + 1 = Nat.card V :=
    (isTree_iff_connected_and_card.mp hF_tree).2
  have hG_mem : G ∈ Finset.univ.filter (fun H : SimpleGraph V => H.IsAcyclic) := by simp [hG]
  have hG_le_max : Nat.card G.edgeSet ≤ Nat.card F.edgeSet := hF_max G hG_mem
  have heq : Nat.card G.edgeSet = Nat.card F.edgeSet := by omega
  haveI := hVne
  refine ⟨fun u v => ?_⟩
  by_contra hnr
  have hacyc' : (G ⊔ edge u v).IsAcyclic := hG.sup_edge_of_not_reachable hnr
  have hmem' : G ⊔ edge u v ∈ Finset.univ.filter (fun H : SimpleGraph V => H.IsAcyclic) := by
    simp [hacyc']
  have hle := hF_max (G ⊔ edge u v) hmem'
  have huv : u ≠ v := fun h => hnr (h ▸ Reachable.refl _)
  have hlt : Nat.card G.edgeSet < Nat.card (G ⊔ edge u v).edgeSet := by
    have hsub : G.edgeSet ⊂ (G ⊔ edge u v).edgeSet := by
      rw [Set.ssubset_iff_of_subset (edgeSet_mono le_sup_left)]
      exact ⟨s(u, v), by simp [huv], by
        intro hmem
        exact absurd (Adj.reachable hmem) hnr⟩
    exact Set.ncard_lt_ncard hsub (Set.toFinite _)
  omega
