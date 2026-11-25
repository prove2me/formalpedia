-- Prove2me | solution 1 for DetDLP.m14a_separator_edge_budget
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T01:41:22.153644+00:00
-- url     : https://prove2.me/submissions/454da05b-bee4-4371-8fca-0481cfc6df42

import Theorems.Thm_DetDLP_lookup_separator_core_contraction

open Finset DetDLP
set_option autoImplicit false

theorem solution {G : BipartiteMultigraph} {m k S D : ℕ}
    (s : LookupSeparatorSpec G m k S D) : 4*m*k ≤ 2*S ∧ G.nE ≤ 3*S := by
  classical
  let I := univ.filter fun e : Fin G.nE =>
    (G.endpoints e).1 ∉ s.lookupVerts ∧ (G.endpoints e).2 ∉ s.lookupVerts
  have hi : I.card ≤ S := s.core_edges_le
  have incl : s.termSubdivVerts ⊆ (I.image fun e => (G.endpoints e).1) ∪
        (I.image fun e => (G.endpoints e).2) := by
    intro v hv
    have hn := (Finset.disjoint_right.mp s.disjoint_verts) hv
    have deg := s.subdiv_deg v hv
    let p : Fin (G.deg v) := ⟨0,by omega⟩
    let q : Fin (G.deg v) := ⟨1,by omega⟩
    let edge (j : Fin (G.deg v)) := (G.ports v).get j
    have incident (j : Fin (G.deg v)) : (G.endpoints (edge j)).1=v ∨ (G.endpoints (edge j)).2=v := by
      have h := List.get_mem (G.ports v) j
      simpa [edge,BipartiteMultigraph.ports] using h
    have surviving : ∃ j, edge j ∈ I := by
      by_contra! hall
      let B := univ.filter fun e : Fin G.nE => ((G.endpoints e).1=v ∧ (G.endpoints e).2∈s.lookupVerts) ∨
        ((G.endpoints e).2=v ∧ (G.endpoints e).1∈s.lookupVerts)
      have mem (j : Fin (G.deg v)) : edge j ∈ B := by
        have no := hall j
        simp only [I,mem_filter,mem_univ,true_and,not_and,not_not] at no
        rcases incident j with h|h
        · exact mem_filter.mpr ⟨mem_univ _, Or.inl ⟨h,no (h ▸ hn)⟩⟩
        · apply mem_filter.mpr; refine ⟨mem_univ _,Or.inr ⟨h,?_⟩⟩
          by_contra bad; exact hn (h ▸ no bad)
      have one : B.card=1 := s.subdiv_one_lookup_edge v hv
      have eq := Finset.card_le_one.mp one.le _ (mem p) _ (mem q)
      have nd : (G.ports v).Nodup := (List.nodup_finRange _).filter _
      have eq' := (List.nodup_iff_injective_get.mp nd) eq
      exact absurd (congrArg Fin.val eq') (by decide : (0:ℕ) ≠ 1)
    obtain ⟨j,hj⟩ := surviving
    rcases incident j with h|h
    · exact mem_union_left _ (mem_image.mpr ⟨edge j,hj,h⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨edge j,hj,h⟩)
  have mass := (Finset.card_le_card incl).trans (Finset.card_union_le ..)
  rw [s.card_termSubdiv] at mass
  have hmass : 4*m*k ≤ 2*S := mass.trans ((Nat.add_le_add (Finset.card_image_le.trans hi) (Finset.card_image_le.trans hi)).trans_eq (by omega))
  have ⟨_,_,_,_,_,_,_,hb,_⟩ := lookup_separator_core_contraction s
  let boundary := fun e : Fin G.nE => (G.endpoints e).1 ∈ s.lookupVerts ∨ (G.endpoints e).2 ∈ s.lookupVerts
  have bCard : (univ.filter boundary).card=4*m*k := by simpa only [Fintype.card_subtype] using hb
  have total := Finset.card_filter_add_card_filter_not (s:=@univ (Fin G.nE) _) boundary
  have complement : (univ.filter (fun e => ¬boundary e)) = I := by ext; simp [boundary,I]
  rw [bCard,complement] at total
  simp only [card_univ,Fintype.card_fin] at total
  exact ⟨hmass,by omega⟩
