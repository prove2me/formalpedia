-- Prove2me | solution 1 for BergeMatching.isMaximum_iff_not_exists_augmenting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:53:24.505427+00:00
-- url     : https://prove2.me/submissions/1840d446-9067-4ab6-9087-0f37785edd9d

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
section
@[expose] public section
open SimpleGraph
namespace BergeMatching
variable {V : Type*}
open Finset in
private lemma ncard_verts_eq_two_mul [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have h := M.spanningCoe.sum_degrees_eq_twice_card_edges
  have hdeg : ∀ v, M.spanningCoe.degree v = if v ∈ M.verts then 1 else 0 := by
    intro v
    rw [Subgraph.degree_spanningCoe]
    split_ifs with hv
    · exact (Subgraph.isMatching_iff_forall_degree.1 hM) v hv
    · exact Subgraph.degree_of_notMem_verts hv
  simp only [hdeg, Finset.sum_boole, Nat.cast_id] at h
  have e1 : M.verts.ncard = #{x | x ∈ M.verts} := by
    rw [← Set.ncard_coe_finset]; congr; ext; simp
  have e2 : M.edgeSet.ncard = #M.spanningCoe.edgeFinset := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset, Subgraph.edgeSet_spanningCoe]
  rw [e1, e2, h]
@[simp] private lemma aug_adj_inl_inr {G : SimpleGraph V} {d : ℕ} {a : V} {i : Fin d} :
    (aug G d).Adj (.inl a) (.inr i) :=
  show _ ∧ _ from ⟨Sum.inl_ne_inr, fun _ _ _ h => by cases h⟩
@[simp] private lemma aug_adj_inr_inl {G : SimpleGraph V} {d : ℕ} {a : V} {i : Fin d} :
    (aug G d).Adj (.inr i) (.inl a) :=
  aug_adj_inl_inr.symm
@[simp] private lemma inl_mem_augSet {U : Set V} {d : ℕ} {a : V} :
    (Sum.inl a : V ⊕ Fin d) ∈ augSet U d ↔ a ∈ U := by
  simp [augSet]
@[simp] private lemma inr_mem_augSet {U : Set V} {d : ℕ} {i : Fin d} :
    (Sum.inr i : V ⊕ Fin d) ∈ augSet U d := by
  simp [augSet]
section BergeHelpers
variable {G : SimpleGraph V}
private lemma deleteVerts_pair_isMatching {M : G.Subgraph} (hM : M.IsMatching) {a b : V}
    (hab : M.Adj a b) : (M.deleteVerts {a, b}).IsMatching := by
  intro x hx
  simp only [Subgraph.deleteVerts_verts, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hx
  obtain ⟨y, hy, hu⟩ := hM hx.1
  have hya : y ≠ a := by
    rintro rfl
    exact hx.2.2 (hM.eq_of_adj_left hy.symm hab)
  have hyb : y ≠ b := by
    rintro rfl
    exact hx.2.1 (hM.eq_of_adj_right hy hab)
  refine ⟨y, ?_, fun z hz => hu z (Subgraph.deleteVerts_adj.1 hz).2.2.2.2⟩
  simp only [Subgraph.deleteVerts_adj, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  exact ⟨hx.1, hx.2, M.edge_vert hy.symm, ⟨hya, hyb⟩, hy⟩
private lemma deleteVerts_pair_adj_iff {M : G.Subgraph} (hM : M.IsMatching) {a b x y : V}
    (hab : M.Adj a b) (hx : x ≠ a) (hy : y ≠ a) :
    (M.deleteVerts {a, b}).Adj x y ↔ M.Adj x y := by
  simp only [Subgraph.deleteVerts_adj, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  refine ⟨fun h => h.2.2.2.2, fun h => ⟨M.edge_vert h, ⟨hx, ?_⟩, M.edge_vert h.symm, ⟨hy, ?_⟩, h⟩⟩
  · rintro rfl; exact hy (hM.eq_of_adj_left h hab.symm)
  · rintro rfl; exact hx (hM.eq_of_adj_right h hab)
private lemma edgeSet_deleteVerts_pair {M : G.Subgraph} (hM : M.IsMatching) {a b : V}
    (hab : M.Adj a b) : (M.deleteVerts {a, b}).edgeSet = M.edgeSet \ {s(a, b)} := by
  ext e
  induction e using Sym2.ind with
  | h x y =>
  simp only [Subgraph.mem_edgeSet, Subgraph.deleteVerts_adj, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or, Set.mem_sdiff]
  constructor
  · rintro ⟨_, ⟨hxa, hxb⟩, _, _, h⟩
    refine ⟨h, fun he => ?_⟩
    rcases Sym2.eq_iff.1 he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hxa rfl
    · exact hxb rfl
  · rintro ⟨h, hne⟩
    have hxa : x ≠ a := by
      rintro rfl; exact hne (by rw [hM.eq_of_adj_left h hab])
    have hxb : x ≠ b := by
      rintro rfl; exact hne (by rw [hM.eq_of_adj_left h hab.symm, Sym2.eq_swap])
    have hya : y ≠ a := by
      rintro rfl; exact hne (by rw [hM.eq_of_adj_right h hab.symm, Sym2.eq_swap])
    have hyb : y ≠ b := by
      rintro rfl; exact hne (by rw [hM.eq_of_adj_right h hab])
    exact ⟨M.edge_vert h, ⟨hxa, hxb⟩, M.edge_vert h.symm, ⟨hya, hyb⟩, h⟩
private lemma ncard_edgeSet_deleteVerts_pair [Finite V] {M : G.Subgraph} (hM : M.IsMatching)
    {a b : V}
    (hab : M.Adj a b) : (M.deleteVerts {a, b}).edgeSet.ncard = M.edgeSet.ncard - 1 := by
  rw [edgeSet_deleteVerts_pair hM hab,
    Set.ncard_sdiff_singleton_of_mem (show s(a, b) ∈ M.edgeSet from hab)]
private lemma not_mem_edgeSet_of_not_mem_verts {M : G.Subgraph} {a b : V} (ha : a ∉ M.verts) :
    s(a, b) ∉ M.edgeSet := fun h => ha (M.edge_vert h)
private lemma IsAugmentingPath.odd_length {M : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hp : IsAugmentingPath M p) : Odd p.length := by
  have hL : p.length ≠ 0 := fun h => hp.2.1 (Walk.eq_of_length_eq_zero h)
  have := hp.2.2.2.2 (p.length - 1) (by omega)
  rw [show p.length - 1 + 1 = p.length by omega, Walk.getVert_length] at this
  have h2 : ¬ Odd (p.length - 1) := fun h => by
    rw [← this, Sym2.eq_swap] at h
    exact not_mem_edgeSet_of_not_mem_verts hp.2.2.2.1 h
  rcases Nat.even_or_odd p.length with h | h
  · exfalso; apply h2
    obtain ⟨k, hk⟩ := h
    exact ⟨k - 1, by omega⟩
  · exact h
private lemma IsAugmentingPath.reverse {M : G.Subgraph} {u v : V} {p : G.Walk u v}
    (hp : IsAugmentingPath M p) : IsAugmentingPath M p.reverse := by
  have hodd := hp.odd_length
  refine ⟨hp.1.reverse, hp.2.1.symm, hp.2.2.2.1, hp.2.2.1, fun i hi => ?_⟩
  rw [Walk.length_reverse] at hi
  rw [Walk.getVert_reverse, Walk.getVert_reverse]
  have := hp.2.2.2.2 (p.length - (i + 1)) (by omega)
  rw [show p.length - (i + 1) + 1 = p.length - i by omega, Sym2.eq_swap] at this
  rw [this]
  obtain ⟨k, hk⟩ := hodd
  rw [Nat.odd_iff, Nat.odd_iff]
  omega
private lemma IsMatching.sup_subgraphOfAdj_deleteVerts {M : G.Subgraph} (hM : M.IsMatching)
    {u w1 w2 : V}
    (h : G.Adj u w1) (hu : u ∉ M.verts) (e1 : M.Adj w1 w2) :
    (M.deleteVerts {w1, w2} ⊔ G.subgraphOfAdj h).IsMatching := by
  refine (deleteVerts_pair_isMatching hM e1).sup (Subgraph.IsMatching.subgraphOfAdj h) ?_
  rw [(deleteVerts_pair_isMatching hM e1).support_eq_verts,
    (Subgraph.IsMatching.subgraphOfAdj h).support_eq_verts, subgraphOfAdj_verts,
    Set.disjoint_left]
  intro x hx hx'
  simp only [Subgraph.deleteVerts_verts, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or] at hx hx'
  rcases hx' with rfl | rfl
  · exact hu hx.1
  · exact hx.2.1 rfl
private theorem exists_larger_of_augmenting [Finite V] :
    ∀ {u v : V} (p : G.Walk u v) (M : G.Subgraph), M.IsMatching → IsAugmentingPath M p →
      ∃ M' : G.Subgraph, M'.IsMatching ∧ M.edgeSet.ncard < M'.edgeSet.ncard
  | _, _, .nil, _, _, hp => absurd rfl hp.2.1
  | _, _, .cons h .nil, M, hM, hp => by
    refine ⟨M ⊔ G.subgraphOfAdj h, hM.sup (Subgraph.IsMatching.subgraphOfAdj h) ?_, ?_⟩
    · rw [hM.support_eq_verts, (Subgraph.IsMatching.subgraphOfAdj h).support_eq_verts,
        subgraphOfAdj_verts, Set.disjoint_left]
      intro x hx hx'
      rcases hx' with rfl | rfl
      · exact hp.2.2.1 hx
      · exact hp.2.2.2.1 hx
    · rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, Set.union_singleton,
        Set.ncard_insert_of_notMem (not_mem_edgeSet_of_not_mem_verts hp.2.2.1)]
      omega
  | u, v, .cons (v := w1) h (.cons (v := w2) h2 r), M, hM, hp => by
    obtain ⟨hpath, huv, hu, hv, he⟩ := hp
    have e1 : M.Adj w1 w2 := by
      have := (he 1 (by simp)).2 odd_one
      simpa using this
    rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.support_cons, List.mem_cons,
      not_or] at hpath
    obtain ⟨⟨hr, hw1⟩, huw1, hur⟩ := hpath
    set M1 := M.deleteVerts {w1, w2} ⊔ G.subgraphOfAdj h with hM1def
    have hM1 : M1.IsMatching := IsMatching.sup_subgraphOfAdj_deleteVerts hM h hu e1
    have hcount : M1.edgeSet.ncard = M.edgeSet.ncard := by
      have hpos : 0 < M.edgeSet.ncard :=
        (Set.ncard_pos (Set.toFinite _)).2 ⟨_, show s(w1, w2) ∈ M.edgeSet from e1⟩
      rw [hM1def, Subgraph.edgeSet_sup, edgeSet_deleteVerts_pair hM e1, edgeSet_subgraphOfAdj,
        Set.union_singleton, Set.ncard_insert_of_notMem
          (fun hm => not_mem_edgeSet_of_not_mem_verts hu hm.1),
        Set.ncard_sdiff_singleton_of_mem (show s(w1, w2) ∈ M.edgeSet from e1)]
      omega
    have hadj : ∀ a b, a ∈ r.support → b ∈ r.support → (M1.Adj a b ↔ M.Adj a b) := by
      intro a b ha hb
      have hau : a ≠ u := fun h' => hur (h' ▸ ha)
      have haw : a ≠ w1 := fun h' => hw1 (h' ▸ ha)
      have hbw : b ≠ w1 := fun h' => hw1 (h' ▸ hb)
      rw [hM1def, Subgraph.sup_adj, subgraphOfAdj_adj, deleteVerts_pair_adj_iff hM e1 haw hbw]
      refine ⟨fun h' => h'.elim id fun he' => ?_, Or.inl⟩
      rcases Sym2.eq_iff.1 he' with ⟨h1, _⟩ | ⟨_, h1⟩
      · exact absurd h1.symm hau
      · exact absurd h1.symm haw
    have hr' : IsAugmentingPath M1 r := by
      refine ⟨hr, ?_, ?_, ?_, fun i hi => ?_⟩
      · rintro rfl; exact hv (M.edge_vert e1.symm)
      · have h2u : w2 ≠ u := fun h' => hur (h' ▸ r.start_mem_support)
        have h2w : w2 ≠ w1 := fun h' => hw1 (h' ▸ r.start_mem_support)
        rw [hM1def, Subgraph.verts_sup, subgraphOfAdj_verts]
        simp [h2u, h2w]
      · have hvu : v ≠ u := fun h' => hur (h' ▸ r.end_mem_support)
        have hvw : v ≠ w1 := fun h' => hw1 (h' ▸ r.end_mem_support)
        rw [hM1def, Subgraph.verts_sup, subgraphOfAdj_verts]
        simp [hv, hvu, hvw]
      · have := he (i + 2) (by simp; omega)
        simp only [Walk.getVert_cons_succ] at this
        rw [Subgraph.mem_edgeSet, hadj _ _ (r.getVert_mem_support _) (r.getVert_mem_support _),
          ← Subgraph.mem_edgeSet, this, Nat.odd_iff, Nat.odd_iff]
        omega
    obtain ⟨M2, hM2, hlt⟩ := exists_larger_of_augmenting r M1 hM1 hr'
    exact ⟨M2, hM2, hcount ▸ hlt⟩
private lemma IsAugmentingPath.of_deleteVerts_pair {M : G.Subgraph} (hM : M.IsMatching)
    {x1 x2 a b : V}
    (hx12 : M.Adj x1 x2) {Q : G.Walk a b} (hQ : IsAugmentingPath (M.deleteVerts {x1, x2}) Q)
    (hQx1 : ∀ w ∈ Q.support, w ≠ x1) (ha : a ≠ x2) (hb : b ≠ x2) : IsAugmentingPath M Q := by
  obtain ⟨hpath, hab, ha0, hb0, he⟩ := hQ
  refine ⟨hpath, hab, fun h => ha0 ?_, fun h => hb0 ?_, fun i hi => ?_⟩
  · simp [h, hQx1 a Q.start_mem_support, ha]
  · simp [h, hQx1 b Q.end_mem_support, hb]
  · rw [← he i hi, Subgraph.mem_edgeSet, Subgraph.mem_edgeSet,
      deleteVerts_pair_adj_iff hM hx12 (hQx1 _ (Q.getVert_mem_support _))
        (hQx1 _ (Q.getVert_mem_support _))]
private lemma IsAugmentingPath.cons_cons_deleteVerts_pair {M : G.Subgraph} (hM : M.IsMatching)
    {x x1 x2 b : V} (hx12 : M.Adj x1 x2) (h : G.Adj x x1) (hx : x ∉ M.verts) {Q : G.Walk x2 b}
    (hQ : IsAugmentingPath (M.deleteVerts {x1, x2}) Q)
    (hQx : ∀ w ∈ Q.support, w ≠ x ∧ w ≠ x1) :
    IsAugmentingPath M (.cons h (.cons (M.adj_sub hx12) Q)) := by
  obtain ⟨hpath, hab, ha0, hb0, he⟩ := hQ
  have hxx1 : x ≠ x1 := h.ne
  refine ⟨?_, fun h' => (hQx b Q.end_mem_support).1 h'.symm, hx, fun h' => hb0 ?_,
    fun i hi => ?_⟩
  · rw [Walk.cons_isPath_iff, Walk.cons_isPath_iff, Walk.support_cons, List.mem_cons, not_or]
    exact ⟨⟨hpath, fun h' => (hQx _ h').2 rfl⟩, hxx1, fun h' => (hQx _ h').1 rfl⟩
  · simp [h', (hQx b Q.end_mem_support).2, hab.symm]
  · rcases i with _ | _ | j
    · simp only [Walk.getVert_zero, zero_add, Walk.getVert_cons_succ]
      simp only [Nat.not_odd_zero, iff_false]
      exact not_mem_edgeSet_of_not_mem_verts hx
    · simp only [zero_add, Walk.getVert_cons_succ, Walk.getVert_zero, odd_one, iff_true]
      exact hx12
    · simp only [Walk.getVert_cons_succ, Walk.length_cons] at hi ⊢
      rw [Subgraph.mem_edgeSet, ← deleteVerts_pair_adj_iff hM hx12
        (hQx _ (Q.getVert_mem_support _)).2 (hQx _ (Q.getVert_mem_support _)).2,
        ← Subgraph.mem_edgeSet, he j (by omega), Nat.odd_iff, Nat.odd_iff]
      omega
private theorem exists_augmenting_aux [Finite V] (n : ℕ) :
    ∀ (F : Set V) (M M' : G.Subgraph), M.IsMatching → M'.IsMatching →
      M'.edgeSet.ncard = n → M.edgeSet.ncard < n → Disjoint M'.verts F →
      ∃ (u v : V) (p : G.Walk u v), IsAugmentingPath M p ∧ ∀ w ∈ p.support, w ∉ F := by
  induction n with
  | zero => intros; omega
  | succ n ih =>
    intro F M M' hM hM' hn hlt hF
    obtain ⟨x, hxM', hxM⟩ : ∃ x, x ∈ M'.verts ∧ x ∉ M.verts := by
      by_contra hcon
      push Not at hcon
      have := Set.ncard_le_ncard hcon
      rw [ncard_verts_eq_two_mul hM, ncard_verts_eq_two_mul hM'] at this
      omega
    obtain ⟨x1, hx1, -⟩ := hM' hxM'
    have hxF : x ∉ F := Set.disjoint_left.1 hF hxM'
    have hx1F : x1 ∉ F := Set.disjoint_left.1 hF (M'.edge_vert hx1.symm)
    have hxx1 : x ≠ x1 := (M'.adj_sub hx1).ne
    by_cases hx1M : x1 ∉ M.verts
    · refine ⟨x, x1, .cons (M'.adj_sub hx1) .nil, ⟨?_, hxx1, hxM, hx1M, ?_⟩, ?_⟩
      · simp [Walk.cons_isPath_iff, hxx1]
      · intro i hi
        simp only [Walk.length_cons, Walk.length_nil, zero_add, Nat.lt_one_iff] at hi
        subst hi
        simp only [Walk.getVert_zero, zero_add, Walk.getVert_cons_succ, Nat.not_odd_zero,
          iff_false]
        exact not_mem_edgeSet_of_not_mem_verts hxM
      · simp [hxF, hx1F]
    · push Not at hx1M
      obtain ⟨x2, hx12, -⟩ := hM hx1M
      have hM0 := deleteVerts_pair_isMatching hM hx12
      have hM0' := deleteVerts_pair_isMatching hM' hx1
      have hn0 : (M'.deleteVerts {x, x1}).edgeSet.ncard = n := by
        rw [ncard_edgeSet_deleteVerts_pair hM' hx1]; omega
      have hlt0 : (M.deleteVerts {x1, x2}).edgeSet.ncard < n := by
        have hpos : 0 < M.edgeSet.ncard :=
          (Set.ncard_pos (Set.toFinite _)).2 ⟨_, show s(x1, x2) ∈ M.edgeSet from hx12⟩
        rw [ncard_edgeSet_deleteVerts_pair hM hx12]; omega
      have hF0 : Disjoint (M'.deleteVerts {x, x1}).verts (insert x (insert x1 F)) := by
        rw [Set.disjoint_left]
        intro a ha
        simp only [Subgraph.deleteVerts_verts, Set.mem_sdiff, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or] at ha ⊢
        exact ⟨ha.2.1, ha.2.2, Set.disjoint_left.1 hF ha.1⟩
      obtain ⟨y, z, P, hP, hPF⟩ := ih _ _ _ hM0 hM0' hn0 hlt0 hF0
      have hPx : ∀ w ∈ P.support, w ≠ x ∧ w ≠ x1 ∧ w ∉ F := by
        intro w hw
        have := hPF w hw
        simp only [Set.mem_insert_iff, not_or] at this
        exact this
      by_cases hy : y = x2
      · subst hy
        refine ⟨x, z, _, hP.cons_cons_deleteVerts_pair hM hx12 (M'.adj_sub hx1) hxM
          fun w hw => ⟨(hPx w hw).1, (hPx w hw).2.1⟩, ?_⟩
        intro w hw
        simp only [Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | rfl | hw
        · exact hxF
        · exact hx1F
        · exact (hPx w hw).2.2
      · by_cases hz : z = x2
        · subst hz
          have hPx' : ∀ w ∈ P.reverse.support, w ≠ x ∧ w ≠ x1 ∧ w ∉ F := by
            intro w hw
            rw [Walk.support_reverse, List.mem_reverse] at hw
            exact hPx w hw
          refine ⟨x, y, _, hP.reverse.cons_cons_deleteVerts_pair hM hx12 (M'.adj_sub hx1) hxM
            fun w hw => ⟨(hPx' w hw).1, (hPx' w hw).2.1⟩, ?_⟩
          intro w hw
          simp only [Walk.support_cons, List.mem_cons] at hw
          rcases hw with rfl | rfl | hw
          · exact hxF
          · exact hx1F
          · exact (hPx' w hw).2.2
        · exact ⟨y, z, P, hP.of_deleteVerts_pair hM hx12 (fun w hw => (hPx w hw).2.1) hy hz,
            fun w hw => (hPx w hw).2.2⟩
end BergeHelpers
end BergeMatching
end
end

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BergeMatching
variable {V : Type*}
namespace BergeMatching
theorem _root_.solution [Finite V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) :
    (∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard) ↔
      ¬ ∃ (u v : V) (p : G.Walk u v), IsAugmentingPath M p := by
  constructor
  · rintro hmax ⟨u, v, p, hp⟩
    obtain ⟨M', hM', hlt⟩ := exists_larger_of_augmenting p M hM hp
    exact absurd (hmax M' hM') (not_le.2 hlt)
  · intro hno M' hM'
    by_contra hlt
    push Not at hlt
    obtain ⟨u, v, p, hp, -⟩ := exists_augmenting_aux _ ∅ M M' hM hM' rfl hlt
      (Set.disjoint_empty _)
    exact hno ⟨u, v, p, hp⟩
end BergeMatching
