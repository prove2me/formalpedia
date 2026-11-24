-- Prove2me | solution 1 for ConstructiveArboricity.Exact.density_and_arboricity
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T16:28:12.643918+00:00
-- url     : https://prove2.me/submissions/83dbbabf-8175-4562-a770-4ae305307d9c

import Mathlib
import Definitions.Def_ConstructiveArboricity_Exact_Graph
open SimpleGraph

namespace NW
variable {V : Type*}

lemma gr_del (S : Set (Sym2 V)) (e : Sym2 V) :
    fromEdgeSet (S \ {e}) = (fromEdgeSet S).deleteEdges {e} := by
  ext x y
  simp [fromEdgeSet_adj]

lemma gr_ins (S : Set (Sym2 V)) (x y : V) (h : x ≠ y) :
    fromEdgeSet (insert s(x,y) S) = fromEdgeSet S ⊔ edge x y := by
  ext u v
  simp only [fromEdgeSet_adj, edge_adj, sup_adj, Set.mem_insert_iff, Sym2.eq_iff]
  grind

lemma acyc_ins {S : Set (Sym2 V)} {x y : V} (h : x ≠ y) (hS : (fromEdgeSet S).IsAcyclic)
    (hn : ¬ (fromEdgeSet S).Reachable x y) : (fromEdgeSet (insert s(x,y) S)).IsAcyclic := by
  rw [gr_ins S x y h]; exact hS.sup_edge_of_not_reachable hn

lemma acyc_del {S : Set (Sym2 V)} (e : Sym2 V) (hS : (fromEdgeSet S).IsAcyclic) :
    (fromEdgeSet (S \ {e})).IsAcyclic :=
  hS.anti (fromEdgeSet_mono Set.sdiff_subset)

lemma bridge {S : Set (Sym2 V)} {x y : V} (hS : (fromEdgeSet S).IsAcyclic)
    (h : s(x,y) ∈ S) (hne : x ≠ y) : ¬ (fromEdgeSet (S \ {s(x,y)})).Reachable x y := by
  rw [gr_del]
  have := (isAcyclic_iff_forall_isBridge.mp hS) (e := s(x,y)) (by simp [h, hne])
  exact isBridge_iff.mp this

/-- an edge of a path in a forest separates the endpoints of the path after deletion -/
lemma sep {S : Set (Sym2 V)} {a b : V} (hS : (fromEdgeSet S).IsAcyclic)
    {p : (fromEdgeSet S).Walk a b} (hp : p.IsPath) {e : Sym2 V} (he : e ∈ p.edges) :
    ¬ (fromEdgeSet (S \ {e})).Reachable a b := by
  intro hr
  obtain ⟨q, hq0⟩ := hr.exists_isPath
  have hle : fromEdgeSet (S \ {e}) ≤ fromEdgeSet S := fromEdgeSet_mono Set.sdiff_subset
  have hq : (q.mapLe hle).IsPath := hq0.mapLe hle
  have := (hS.subsingleton_path a b).elim ⟨p, hp⟩ ⟨q.mapLe hle, hq⟩
  have h2 : p = q.mapLe hle := congrArg Subtype.val this
  rw [h2, Walk.edges_mapLe_eq_edges] at he
  have := q.edges_subset_edgeSet he
  simp [edgeSet_fromEdgeSet] at this
  exact this.1.2 this.2


open Classical in
/-- vertices reachable from `a` using the edges of `S` -/
noncomputable def comp [Fintype V] (S : Set (Sym2 V)) (a : V) : Finset V :=
  Finset.univ.filter fun x => (fromEdgeSet S).Reachable a x

lemma mem_comp [Fintype V] {S : Set (Sym2 V)} {a x : V} :
    x ∈ comp S a ↔ (fromEdgeSet S).Reachable a x := by
  classical simp [comp]

lemma comp_mono [Fintype V] {S S' : Set (Sym2 V)} (h : S ⊆ S') (a : V) :
    comp S a ⊆ comp S' a := fun x hx =>
  mem_comp.mpr ((mem_comp.mp hx).mono (fromEdgeSet_mono h))

lemma reach_ins {S : Set (Sym2 V)} {a u w : V} (hu : ¬ (fromEdgeSet S).Reachable a u)
    (hw : ¬ (fromEdgeSet S).Reachable a w) {x : V}
    (h : (fromEdgeSet (insert s(u,w) S)).Reachable a x) : (fromEdgeSet S).Reachable a x := by
  have key : ∀ y x : V, ∀ p : (fromEdgeSet (insert s(u,w) S)).Walk y x,
      (fromEdgeSet S).Reachable a y → (fromEdgeSet S).Reachable a x := by
    intro y x p
    induction p with
    | nil => exact id
    | cons hadj q ih =>
      rename_i y y' x
      intro hy
      apply ih
      rw [fromEdgeSet_adj] at hadj
      rcases hadj with ⟨h1 | h1, h2⟩
      · rcases Sym2.eq_iff.mp h1 with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · subst e1; exact absurd hy hu
        · subst e1; exact absurd hy hw
      · exact hy.trans (Adj.reachable (by simp [fromEdgeSet_adj, h1, h2]))
  obtain ⟨p⟩ := h
  exact key a x p (Reachable.refl a)


section shrink
variable [Fintype V]

lemma shrinkA {S : Set (Sym2 V)} (hS : (fromEdgeSet S).IsAcyclic) {a p q : V} (hne : p ≠ q)
    (hd : s(p,q) ∈ S) (hp : p ∈ comp S a) :
    (comp (S \ {s(p,q)}) a).card < (comp S a).card := by
  have hq : q ∈ comp S a := by
    rw [mem_comp] at hp ⊢
    exact hp.trans (Adj.reachable (by simp [fromEdgeSet_adj, hd, hne]))
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (comp_mono Set.sdiff_subset a)]
  by_cases h : q ∈ comp (S \ {s(p,q)}) a
  · refine ⟨p, hp, fun hp' => ?_⟩
    exact bridge hS hd hne ((mem_comp.mp hp').symm.trans (mem_comp.mp h))
  · exact ⟨q, hq, h⟩

lemma shrinkB {S : Set (Sym2 V)} (hS : (fromEdgeSet S).IsAcyclic) {a v1 z : V} (d : Sym2 V)
    (hv1 : v1 ∈ comp S a) (hz : z ∉ comp S a) (hne : v1 ≠ z)
    (hsep : v1 ∉ comp (S \ {d}) a) :
    (fromEdgeSet (insert s(v1,z) (S \ {d}))).IsAcyclic ∧
    (comp (insert s(v1,z) (S \ {d})) a).card < (comp S a).card := by
  have hzA : z ∉ comp (S \ {d}) a := fun h => hz (comp_mono Set.sdiff_subset a h)
  constructor
  · apply acyc_ins hne (acyc_del d hS)
    intro hr
    apply hz
    rw [mem_comp] at hv1 ⊢
    exact hv1.trans (hr.mono (fromEdgeSet_mono Set.sdiff_subset))
  · have hsub : comp (insert s(v1,z) (S \ {d})) a ⊆ comp (S \ {d}) a := fun x hx =>
      mem_comp.mpr (reach_ins (fun h => hsep (mem_comp.mpr h)) (fun h => hzA (mem_comp.mpr h))
        (mem_comp.mp hx))
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset (hsub.trans (comp_mono Set.sdiff_subset a))]
    exact ⟨v1, hv1, fun h => hsep (hsub h)⟩
end shrink

section coloring
open Classical
variable {k : ℕ}

def cls (E : Finset (Sym2 V)) (c : Sym2 V → Fin (k+1)) (i : Fin (k+1)) : Set (Sym2 V) :=
  {f | f ∈ E ∧ c f = i}

def Valid (E : Finset (Sym2 V)) (c : Sym2 V → Fin (k+1)) : Prop :=
  ∀ i, (fromEdgeSet (cls E c i)).IsAcyclic

lemma valid_move {E : Finset (Sym2 V)} {c : Sym2 V → Fin (k+1)} (hv : Valid E c) {d : Sym2 V}
    {i : Fin (k+1)} (hd : d ∈ E) (hcd : c d = 0) (hi : i ≠ 0)
    (hacyc : (fromEdgeSet (insert d (cls E c i))).IsAcyclic) :
    Valid E (Function.update c d i) ∧ cls E (Function.update c d i) 0 = cls E c 0 \ {d} := by
  have hi' : (0 : Fin (k+1)) ≠ i := Ne.symm hi
  have k0 : cls E (Function.update c d i) 0 = cls E c 0 \ {d} := by
    ext f
    by_cases hf : f = d
    · subst hf; simp [cls, Function.update_apply, hi', hi]
    · simp [cls, Function.update_apply, hf]
  have ki : cls E (Function.update c d i) i = insert d (cls E c i) := by
    ext f
    by_cases hf : f = d
    · subst hf; simp [cls, Function.update_apply, hd, hi]
    · simp [cls, Function.update_apply, hf]
  have kj : ∀ j, j ≠ 0 → j ≠ i → cls E (Function.update c d i) j = cls E c j := by
    intro j h0 hj
    ext f
    by_cases hf : f = d
    · subst hf; simp [cls, Function.update_apply, hcd, Ne.symm h0, Ne.symm hj, h0]
    · simp [cls, Function.update_apply, hf]
  refine ⟨fun j => ?_, k0⟩
  by_cases hj : j = i
  · subst hj; rw [ki]; exact hacyc
  · by_cases h0 : j = 0
    · subst h0; rw [k0]; exact acyc_del _ (hv 0)
    · rw [kj j h0 hj]; exact hv j

lemma valid_swap {E : Finset (Sym2 V)} {c : Sym2 V → Fin (k+1)} (hv : Valid E c) {d e1 : Sym2 V}
    {i : Fin (k+1)} (hd : d ∈ E) (he1 : e1 ∈ E) (hcd : c d = 0) (hce : c e1 = i) (hi : i ≠ 0)
    (h0 : (fromEdgeSet (insert e1 (cls E c 0 \ {d}))).IsAcyclic)
    (hi' : (fromEdgeSet (insert d (cls E c i \ {e1}))).IsAcyclic) :
    Valid E (Function.update (Function.update c d i) e1 0) ∧
      cls E (Function.update (Function.update c d i) e1 0) 0 = insert e1 (cls E c 0 \ {d}) := by
  have hde : d ≠ e1 := by
    rintro rfl; rw [hcd] at hce; exact hi hce.symm
  have hi0 : (0 : Fin (k+1)) ≠ i := Ne.symm hi
  have k0 : cls E (Function.update (Function.update c d i) e1 0) 0 =
      insert e1 (cls E c 0 \ {d}) := by
    ext f
    by_cases hf : f = e1
    · subst hf; simp [cls, Function.update_apply, he1, hi, hi0]
    · by_cases hf' : f = d
      · subst hf'; simp [cls, Function.update_apply, hf, hi0, hi]
      · simp [cls, Function.update_apply, hf, hf']
  have ki : cls E (Function.update (Function.update c d i) e1 0) i =
      insert d (cls E c i \ {e1}) := by
    ext f
    by_cases hf : f = e1
    · subst hf; simp [cls, Function.update_apply, hde, hi, hi0, hde.symm]
    · by_cases hf' : f = d
      · subst hf'; simp [cls, Function.update_apply, hf, hd]
      · simp [cls, Function.update_apply, hf, hf']
  have kj : ∀ j, j ≠ 0 → j ≠ i →
      cls E (Function.update (Function.update c d i) e1 0) j = cls E c j := by
    intro j hj0 hj
    ext f
    by_cases hf : f = e1
    · subst hf; simp [cls, Function.update_apply, hde, hce, Ne.symm hj0, Ne.symm hj, hj]
    · by_cases hf' : f = d
      · subst hf'; simp [cls, Function.update_apply, hf, hcd, Ne.symm hj0, hj0, Ne.symm hj]
      · simp [cls, Function.update_apply, hf, hf']
  refine ⟨fun j => ?_, k0⟩
  by_cases hj : j = 0
  · subst hj; rw [k0]; exact h0
  · by_cases hj' : j = i
    · subst hj'; rw [ki]; exact hi'
    · rw [kj j hj hj']; exact hv j
end coloring

section peculiar
variable [Fintype V]

def TCset (T : Set (Sym2 V)) (C : Finset V) : Set (Sym2 V) := {f | f ∈ T ∧ ∀ v ∈ f, v ∈ C}

lemma tc_reach_mem {T : Set (Sym2 V)} {C : Finset V} {y w : V}
    (h : (fromEdgeSet (TCset T C)).Reachable y w) (hy : y ∉ C) : y = w := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => rfl
  | cons hadj _ =>
    exfalso
    rw [fromEdgeSet_adj] at hadj
    exact hy (hadj.1.2 _ (Sym2.mem_mk_left _ _))

lemma walk_L {T S : Set (Sym2 V)} (hST : S ⊆ T) (C : Finset V) {w : V} (hw : w ∈ C) :
    ∀ {x : V} (W : (fromEdgeSet S).Walk x w), ¬ (fromEdgeSet (TCset T C)).Reachable x w →
    ∃ z v, s(z,v) ∈ W.edges ∧ z ∉ C ∧ v ∈ C ∧ s(z,v) ∈ S ∧
      (fromEdgeSet (TCset T C)).Reachable v w := by
  intro x W
  induction W with
  | nil => intro h; exact absurd (Reachable.refl _) h
  | @cons x x' w hadj W' ih =>
    intro hn
    have hmem : s(x,x') ∈ S := ((fromEdgeSet_adj _).mp hadj).1
    by_cases hx' : x' ∈ C
    · by_cases hx : x ∈ C
      · have hadjTC : (fromEdgeSet (TCset T C)).Adj x x' := by
          rw [fromEdgeSet_adj]
          refine ⟨⟨hST hmem, ?_⟩, hadj.ne⟩
          intro v hv
          rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact hx
          · exact hx'
        obtain ⟨z, v, h1, h2, h3, h4, h5⟩ := ih hw (fun hr => hn (hadjTC.reachable.trans hr))
        exact ⟨z, v, by simp [h1], h2, h3, h4, h5⟩
      · by_cases hr : (fromEdgeSet (TCset T C)).Reachable x' w
        · exact ⟨x, x', by simp, hx, hx', hmem, hr⟩
        · obtain ⟨z, v, h1, h2, h3, h4, h5⟩ := ih hw hr
          exact ⟨z, v, by simp [h1], h2, h3, h4, h5⟩
    · obtain ⟨z, v, h1, h2, h3, h4, h5⟩ := ih hw (fun hr => by
        have := tc_reach_mem hr hx'
        subst this; exact hx' hw)
      exact ⟨z, v, by simp [h1], h2, h3, h4, h5⟩

lemma sub_comp {T : Set (Sym2 V)} {e' e1 : Sym2 V} {v1 v1' : V} (hv1 : v1 ∈ e1)
    (hn : v1 ∉ comp (T \ {e'}) v1') (hmem : v1' ∈ comp (T \ {e1}) v1) :
    comp (T \ {e'}) v1' ⊆ comp (T \ {e1}) v1 := by
  intro x hx
  have key : ∀ y x : V, ∀ p : (fromEdgeSet (T \ {e'})).Walk y x,
      (fromEdgeSet (T \ {e'})).Reachable v1' y → (fromEdgeSet (T \ {e1})).Reachable v1 y →
      (fromEdgeSet (T \ {e1})).Reachable v1 x := by
    intro y x p
    induction p with
    | nil => exact fun _ h => h
    | @cons y y' x hadj q ih =>
      intro hy hy1
      have hy' : (fromEdgeSet (T \ {e'})).Reachable v1' y' := hy.trans hadj.reachable
      apply ih hy' 
      refine hy1.trans (Adj.reachable ?_)
      rw [fromEdgeSet_adj] at hadj ⊢
      refine ⟨⟨hadj.1.1, ?_⟩, hadj.2⟩
      intro h
      simp only [Set.mem_singleton_iff] at h
      rw [← h] at hv1
      rcases Sym2.mem_iff.mp hv1 with rfl | rfl
      · exact hn (mem_comp.mpr hy)
      · exact hn (mem_comp.mpr hy')
  exact mem_comp.mpr (key v1' x (mem_comp.mp hx).some (Reachable.refl _) (mem_comp.mp hmem))

def PecP (T : Set (Sym2 V)) (C : Finset V) (a v z : V) : Prop :=
  v ∈ C ∧ z ∉ C ∧ s(v,z) ∈ T ∧ ¬ (fromEdgeSet (T \ {s(v,z)})).Reachable v a

lemma tc_sub_del {T : Set (Sym2 V)} {C : Finset V} {v z : V} (hz : z ∉ C) :
    TCset T C ⊆ T \ {s(v,z)} := by
  intro f hf
  refine ⟨hf.1, ?_⟩
  intro h
  simp only [Set.mem_singleton_iff] at h
  subst h
  exact hz (hf.2 z (Sym2.mem_mk_right _ _))

lemma peculiar {T : Set (Sym2 V)} (hT : (fromEdgeSet T).IsAcyclic) (C : Finset V) {a w0 : V}
    (haC : a ∈ C) (hw0 : w0 ∈ C) (hreach : (fromEdgeSet T).Reachable a w0)
    (hn : ¬ (fromEdgeSet (TCset T C)).Reachable a w0) :
    ∃ v1 z, v1 ∈ C ∧ z ∉ C ∧ s(v1,z) ∈ T ∧ ¬ (fromEdgeSet (TCset T C)).Reachable a v1 ∧
      ∀ w ∈ C, (fromEdgeSet (T \ {s(v1,z)})).Reachable v1 w →
        (fromEdgeSet (TCset T C)).Reachable v1 w := by
  classical
  have hle : ∀ e : Sym2 V, fromEdgeSet (T \ {e}) ≤ fromEdgeSet T :=
    fun e => fromEdgeSet_mono Set.sdiff_subset
  -- an initial pair
  have hinit : ∃ p : V × V, PecP T C a p.1 p.2 := by
    obtain ⟨W, hW⟩ := hreach.exists_isPath
    obtain ⟨z0, v0, he0, hz0, hv0, hS0, hr0⟩ :=
      walk_L (S := T) (subset_refl T) C hw0 W hn
    rw [Sym2.eq_swap] at he0 hS0
    refine ⟨(v0, z0), hv0, hz0, hS0, fun h => ?_⟩
    apply sep hT hW he0
    exact h.symm.trans (hr0.mono (fromEdgeSet_mono (tc_sub_del hz0)))
  obtain ⟨⟨v1, z⟩, hmem, hmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun p : V × V => PecP T C a p.1 p.2))
    (fun p => (comp (T \ {s(p.1,p.2)}) p.1).card)
    (by obtain ⟨p, hp⟩ := hinit; exact ⟨p, by simpa using hp⟩)
  have hP : PecP T C a v1 z := by simpa using hmem
  obtain ⟨hv1, hz, hS1, hsep1⟩ := hP
  refine ⟨v1, z, hv1, hz, hS1, fun h => hsep1 ((h.mono (fromEdgeSet_mono (tc_sub_del hz))).symm),
    ?_⟩
  intro w hwC hr
  by_contra hnw
  obtain ⟨q, hq⟩ := hr.exists_isPath
  obtain ⟨z', v', he', hz', hv', hS', hrw⟩ :=
    walk_L (S := T \ {s(v1,z)}) Set.sdiff_subset C hwC q hnw
  have e2 : s(z',v') = s(v',z') := Sym2.eq_swap
  rw [e2] at he' hS'
  have hqT : (q.mapLe (hle s(v1,z))).IsPath := hq.mapLe _
  have he'T : s(v',z') ∈ (q.mapLe (hle s(v1,z))).edges := by
    rw [Walk.edges_mapLe_eq_edges]; exact he'
  have F1 := sep hT hqT he'T
  have F2 : v1 ∉ comp (T \ {s(v',z')}) v' := by
    intro h
    apply F1
    exact (mem_comp.mp h).symm.trans (hrw.mono (fromEdgeSet_mono (tc_sub_del hz')))
  have hv'mem : v' ∈ comp (T \ {s(v1,z)}) v1 := by
    have : v' ∈ q.support := Walk.fst_mem_support_of_mem_edges q he'
    exact mem_comp.mpr ⟨q.takeUntil v' this⟩
  have F3 := sub_comp (T := T) (Sym2.mem_mk_left v1 z) F2 hv'mem
  have hP' : PecP T C a v' z' := by
    refine ⟨hv', hz', hS'.1, fun h => hsep1 ?_⟩
    have : a ∈ comp (T \ {s(v',z')}) v' := mem_comp.mpr h
    exact (mem_comp.mp (F3 this))
  have hle' := hmin (v', z') (by simpa using hP')
  have hlt : (comp (T \ {s(v',z')}) v').card < (comp (T \ {s(v1,z)}) v1).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset F3]
    exact ⟨v1, mem_comp.mpr (Reachable.refl _), F2⟩
  simp only at hle'
  omega
end peculiar

section aux
open Classical
variable [Fintype V]

lemma conn_card (S : Finset (Sym2 V)) (C : Finset V) (hCne : C.Nonempty)
    (hS : ∀ f ∈ S, ∀ v ∈ f, v ∈ C)
    (hconn : ∀ x ∈ C, ∀ y ∈ C, (fromEdgeSet (S : Set (Sym2 V))).Reachable x y) :
    C.card ≤ S.card + 1 := by
  let G : SimpleGraph C := (fromEdgeSet (S : Set (Sym2 V))).comap (Subtype.val : C → V)
  have lift : ∀ x y : V, ∀ p : (fromEdgeSet (S : Set (Sym2 V))).Walk x y, ∀ (hx : x ∈ C)
      (hy : y ∈ C), G.Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
    intro x y p
    induction p with
    | nil => intro hx hy; exact Reachable.refl _
    | @cons x x' y hadj q ih =>
      intro hx hy
      have hm : s(x,x') ∈ S := by
        have := ((fromEdgeSet_adj _).mp hadj).1
        simpa using this
      have hx' : x' ∈ C := hS _ hm x' (Sym2.mem_mk_right _ _)
      exact (Adj.reachable (by simpa [G] using hadj)).trans (ih hx' hy)
  have hconn' : G.Connected := by
    haveI : Nonempty C := hCne.to_subtype
    refine ⟨fun x y => ?_⟩
    obtain ⟨p⟩ := hconn x x.2 y y.2
    exact lift x y p x.2 y.2
  have h1 := hconn'.card_vert_le_card_edgeSet_add_one
  have h2 : Nat.card G.edgeSet ≤ S.card := by
    have : Nat.card G.edgeSet ≤ Nat.card (S : Set (Sym2 V)) := by
      refine Nat.card_le_card_of_injective
        (fun e => ⟨Sym2.map Subtype.val e.1, ?_⟩) ?_
      · obtain ⟨e, he⟩ := e
        induction e using Sym2.ind with
        | h x y =>
          have := (fromEdgeSet_adj _).mp (by simpa [G] using he : (fromEdgeSet (S : Set (Sym2 V))).Adj x y)
          simpa using this.1
      · intro e1 e2 h
        apply Subtype.ext
        apply Sym2.map.injective Subtype.val_injective
        exact congrArg Subtype.val h
    simpa using this
  have h3 : Nat.card C = C.card := by simp
  omega

lemma reach_tc {S : Set (Sym2 V)} {a : V} :
    ∀ {y x : V} (p : (fromEdgeSet S).Walk y x), (fromEdgeSet S).Reachable a y →
      (fromEdgeSet (TCset S (comp S a))).Reachable y x := by
  intro y x p
  induction p with
  | nil => intro _; exact Reachable.refl _
  | @cons y y' x hadj q ih =>
    intro hy
    have hy' : (fromEdgeSet S).Reachable a y' := hy.trans hadj.reachable
    refine Adj.reachable ?_ |>.trans (ih hy')
    rw [fromEdgeSet_adj] at hadj ⊢
    refine ⟨⟨hadj.1, ?_⟩, hadj.2⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact mem_comp.mpr hy
    · exact mem_comp.mpr hy'

lemma reach_transfer {S T : Set (Sym2 V)}
    (h : ∀ p q, (fromEdgeSet S).Adj p q → (fromEdgeSet T).Reachable p q) {x y : V}
    (hr : (fromEdgeSet S).Reachable x y) : (fromEdgeSet T).Reachable x y := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj q ih => exact (h _ _ hadj).trans ih

lemma edge_cross {S : Set (Sym2 V)} (D : V → Prop) :
    ∀ {x y : V} (W : (fromEdgeSet S).Walk x y), ¬ D x → D y →
      ∃ p q, s(p,q) ∈ W.edges ∧ ¬ D p ∧ D q := by
  intro x y W
  induction W with
  | nil => intro h1 h2; exact absurd h2 h1
  | @cons x x' y hadj q ih =>
    intro hx hy
    by_cases hx' : D x'
    · exact ⟨x, x', by simp, hx, hx'⟩
    · obtain ⟨p, q', h1, h2, h3⟩ := ih hx' hy
      exact ⟨p, q', by simp [h1], h2, h3⟩

lemma valid_add {k : ℕ} {E : Finset (Sym2 V)} {c : Sym2 V → Fin (k+1)} {e : Sym2 V}
    (he : e ∈ E) (hv : Valid (E.erase e) c)
    (hacyc : (fromEdgeSet (insert e (cls (E.erase e) c 0))).IsAcyclic) :
    Valid E (Function.update c e 0) := by
  have key : ∀ j, cls E (Function.update c e 0) j =
      if j = 0 then insert e (cls (E.erase e) c 0) else cls (E.erase e) c j := by
    intro j
    ext f
    by_cases hf : f = e
    · subst hf
      by_cases hj : j = 0
      · simp [cls, Function.update_apply, hj, he]
      · have hj' : (0 : Fin (k+1)) ≠ j := fun h => hj h.symm
        simp [cls, Function.update_apply, hj, hj', he]
    · by_cases hj : j = 0 <;> simp [cls, Function.update_apply, hj, hf, Finset.mem_erase]
  intro j
  rw [key]
  by_cases hj : j = 0
  · simp [hj]; subst hj; exact hacyc
  · simp [hj]; exact hv j
end aux

section core
open Classical
variable [Fintype V]

/-- counting step: some colour class has too few edges inside `C`. -/
lemma exists_light {k : ℕ} (E : Finset (Sym2 V)) (c : Sym2 V → Fin (k+1)) (e : Sym2 V)
    (he : e ∈ E) (C : Finset V) (heC : ∀ v ∈ e, v ∈ C)
    (dens : (E.filter (fun f => ∀ v ∈ f, v ∈ C)).card ≤ (k+1) * (C.card - 1)) :
    ∃ i : Fin (k+1),
      ((E.erase e).filter (fun f => c f = i ∧ ∀ v ∈ f, v ∈ C)).card + 1 < C.card := by
  by_contra hcon
  push_neg at hcon
  have hmem : e ∈ E.filter (fun f => ∀ v ∈ f, v ∈ C) := Finset.mem_filter.mpr ⟨he, heC⟩
  have h1 : ((E.erase e).filter (fun f => ∀ v ∈ f, v ∈ C)).card + 1 =
      (E.filter (fun f => ∀ v ∈ f, v ∈ C)).card := by
    rw [Finset.filter_erase, Finset.card_erase_of_mem hmem]
    have := Finset.card_pos.mpr ⟨e, hmem⟩
    omega
  have h2 := Finset.card_eq_sum_card_fiberwise (s := (E.erase e).filter (fun f => ∀ v ∈ f, v ∈ C))
    (t := Finset.univ) (f := c) (fun x _ => Finset.mem_univ _)
  have h3 : ∀ i : Fin (k+1), C.card - 1 ≤
      (((E.erase e).filter (fun f => ∀ v ∈ f, v ∈ C)).filter (fun f => c f = i)).card := by
    intro i
    have := hcon i
    have h4 : ((E.erase e).filter (fun f => ∀ v ∈ f, v ∈ C)).filter (fun f => c f = i) =
        (E.erase e).filter (fun f => c f = i ∧ ∀ v ∈ f, v ∈ C) := by
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro f _
      tauto
    rw [h4]; omega
  have h5 : (k+1) * (C.card - 1) ≤ ∑ i : Fin (k+1),
      (((E.erase e).filter (fun f => ∀ v ∈ f, v ∈ C)).filter (fun f => c f = i)).card := by
    calc (k+1) * (C.card - 1) = ∑ _i : Fin (k+1), (C.card - 1) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => h3 i)
  have h6 := Finset.card_pos.mpr ⟨e, hmem⟩
  omega


lemma tc_coe {k : ℕ} (E' : Finset (Sym2 V)) (c : Sym2 V → Fin (k+1)) (i : Fin (k+1)) (C : Finset V) :
    ((E'.filter (fun f => c f = i ∧ ∀ v ∈ f, v ∈ C) : Finset (Sym2 V)) : Set (Sym2 V)) =
      TCset (cls E' c i) C := by
  ext f
  simp only [Finset.coe_filter, Set.mem_setOf_eq, TCset, cls]
  tauto

lemma core_step {k : ℕ} (E : Finset (Sym2 V))
    (dens : ∀ W : Finset V, W.Nonempty →
      (E.filter (fun f => ∀ v ∈ f, v ∈ W)).card ≤ (k+1) * (W.card - 1))
    {a b : V} (hab : a ≠ b) (hmem : s(a,b) ∈ E)
    (c : Sym2 V → Fin (k+1)) (hv : Valid (E.erase s(a,b)) c) :
    (∃ c' : Sym2 V → Fin (k+1), Valid E c') ∨ ∃ c' : Sym2 V → Fin (k+1), Valid (E.erase s(a,b)) c' ∧
      (comp (cls (E.erase s(a,b)) c' 0) a).card < (comp (cls (E.erase s(a,b)) c 0) a).card := by
  have hF0ac : (fromEdgeSet (cls (E.erase s(a,b)) c 0)).IsAcyclic := hv 0
  by_cases hb : (fromEdgeSet (cls (E.erase s(a,b)) c 0)).Reachable a b
  swap
  · left
    exact ⟨Function.update c s(a,b) 0, valid_add hmem hv (acyc_ins hab hF0ac hb)⟩
  right
  generalize hE' : E.erase s(a,b) = E' at hv hF0ac hb ⊢
  generalize hF0 : cls E' c 0 = F0 at hF0ac hb ⊢
  have hF0def : F0 = cls E' c 0 := hF0.symm
  generalize hC : comp F0 a = C
  have haC : a ∈ C := hC ▸ mem_comp.mpr (Reachable.refl _)
  have hbC : b ∈ C := hC ▸ mem_comp.mpr hb
  have hconn0 : ∀ x ∈ C, ∀ y ∈ C, (fromEdgeSet (TCset F0 C)).Reachable x y := by
    have h1 : ∀ x ∈ C, (fromEdgeSet (TCset F0 C)).Reachable a x := by
      intro x hx
      rw [← hC] at hx ⊢
      exact reach_tc (mem_comp.mp hx).some (Reachable.refl a)
    intro x hx y hy
    exact (h1 x hx).symm.trans (h1 y hy)
  obtain ⟨i, hi⟩ := exists_light E c s(a,b) hmem C
    (by intro v hx; rcases Sym2.mem_iff.mp hx with rfl | rfl <;> assumption)
    (dens C ⟨a, haC⟩)
  rw [hE'] at hi
  have hi0 : i ≠ 0 := by
    rintro rfl
    have := conn_card (E'.filter (fun f => c f = _ ∧ ∀ v ∈ f, v ∈ C)) C ⟨a, haC⟩
      (fun f hf v hvf => (Finset.mem_filter.mp hf).2.2 v hvf)
      (by rw [tc_coe, ← hF0def]; exact hconn0)
    omega
  have hT : (fromEdgeSet (cls E' c i)).IsAcyclic := hv i
  have hn : ¬ ∀ x ∈ C, ∀ y ∈ C, (fromEdgeSet (TCset (cls E' c i) C)).Reachable x y := by
    intro h
    have := conn_card (E'.filter (fun f => c f = _ ∧ ∀ v ∈ f, v ∈ C)) C ⟨a, haC⟩
      (fun f hf v hvf => (Finset.mem_filter.mp hf).2.2 v hvf)
      (by rw [tc_coe]; exact h)
    omega
  push_neg at hn
  obtain ⟨u, hu, w, hw, hnuw⟩ := hn
  by_cases hA : ∃ p q, s(p,q) ∈ F0 ∧ p ∈ C ∧ p ≠ q ∧
      ¬ (fromEdgeSet (cls E' c i)).Reachable p q
  · obtain ⟨p, q, hd, hpC, hpq, hnr⟩ := hA
    have hd' : s(p,q) ∈ cls E' c 0 := hF0def ▸ hd
    obtain ⟨hvalid, hcls⟩ := valid_move hv hd'.1 hd'.2 hi0 (acyc_ins hpq hT hnr)
    refine ⟨_, hvalid, ?_⟩
    rw [hcls, ← hF0def, ← hC]
    rw [← hC] at hpC
    exact shrinkA hF0ac hpq hd hpC
  · push_neg at hA
    have hall : ∀ x ∈ C, (fromEdgeSet (cls E' c i)).Reachable a x := by
      intro x hx
      have h1 : (fromEdgeSet (TCset F0 C)).Reachable a x := by
        rw [← hC] at hx ⊢
        exact reach_tc (mem_comp.mp hx).some (Reachable.refl a)
      refine reach_transfer ?_ h1
      intro p q hadj
      rw [fromEdgeSet_adj] at hadj
      exact hA p q hadj.1.1 (hadj.1.2 p (Sym2.mem_mk_left _ _)) hadj.2
    have hw0 : ∃ w0 ∈ C, ¬ (fromEdgeSet (TCset (cls E' c i) C)).Reachable a w0 := by
      by_cases h1 : (fromEdgeSet (TCset (cls E' c i) C)).Reachable a u
      · exact ⟨w, hw, fun h2 => hnuw (h1.symm.trans h2)⟩
      · exact ⟨u, hu, h1⟩
    obtain ⟨w0, hw0C, hnw0⟩ := hw0
    obtain ⟨v1, z, hv1, hz, hS1, hna, hprop⟩ := peculiar hT C haC hw0C (hall w0 hw0C) hnw0
    have hv1' : v1 ∈ comp F0 a := by rw [hC]; exact hv1
    have hz' : z ∉ comp F0 a := by rw [hC]; exact hz
    obtain ⟨W, hW⟩ := (mem_comp.mp hv1').exists_isPath
    obtain ⟨p, q, hpq, hpD, hqD⟩ := edge_cross
      (fun x => (fromEdgeSet (TCset (cls E' c i) C)).Reachable v1 x) W
      (fun h => hna h.symm) (Reachable.refl _)
    have hadj := W.adj_of_mem_edges hpq
    rw [fromEdgeSet_adj] at hadj
    have hne : p ≠ q := hadj.2
    have hsep : ¬ (fromEdgeSet (F0 \ {s(p,q)})).Reachable a v1 := sep hF0ac hW hpq
    have hqC : q ∈ C := by
      by_contra hq
      have := tc_reach_mem hqD.symm hq
      rw [this] at hq
      exact hq hv1
    have hpC : p ∈ C := by
      rw [← hC] at hqC ⊢
      exact mem_comp.mpr ((mem_comp.mp hqC).trans (Adj.reachable (by
        rw [fromEdgeSet_adj]; exact ⟨by rw [Sym2.eq_swap]; exact hadj.1, hne.symm⟩)))
    have hvz : v1 ≠ z := fun h => hz (h ▸ hv1)
    have hsepC : v1 ∉ comp (F0 \ {s(p,q)}) a := fun h => hsep (mem_comp.mp h)
    obtain ⟨h0, hcard⟩ := shrinkB hF0ac (d := s(p,q)) hv1' hz' hvz hsepC
    have hi' : (fromEdgeSet (insert s(p,q) (cls E' c i \ {s(v1,z)}))).IsAcyclic := by
      apply acyc_ins hne (acyc_del _ hT)
      intro hr
      have h1 : (fromEdgeSet (cls E' c i \ {s(v1,z)})).Reachable v1 q :=
        hqD.mono (fromEdgeSet_mono (tc_sub_del hz))
      exact hpD (hprop p hpC (h1.trans hr.symm))
    have hd' : s(p,q) ∈ cls E' c 0 := hF0def ▸ hadj.1
    obtain ⟨hvalid, hcls⟩ := valid_swap hv hd'.1 hS1.1 hd'.2 hS1.2 hi0
      (by rw [← hF0def]; exact h0) hi'
    refine ⟨_, hvalid, ?_⟩
    rw [hcls, ← hF0def, ← hC]
    exact hcard


theorem nash_williams {k : ℕ} :
    ∀ (n : ℕ) (E : Finset (Sym2 V)), E.card = n → (∀ f ∈ E, ¬ f.IsDiag) →
      (∀ W : Finset V, W.Nonempty →
        (E.filter (fun f => ∀ v ∈ f, v ∈ W)).card ≤ (k+1) * (W.card - 1)) →
      ∃ c : Sym2 V → Fin (k+1), Valid E c := by
  intro n
  induction n with
  | zero =>
    intro E hn _ _
    have : E = ∅ := Finset.card_eq_zero.mp hn
    subst this
    refine ⟨fun _ => 0, fun i => ?_⟩
    have : cls (∅ : Finset (Sym2 V)) (fun _ => (0 : Fin (k+1))) i = ∅ := by
      ext f; simp [cls]
    rw [this]
    simp
  | succ n ih =>
    intro E hn hE dens
    obtain ⟨e, he⟩ : E.Nonempty := Finset.card_pos.mp (by omega)
    induction e using Sym2.ind with
    | h a b =>
    have hab : a ≠ b := fun h => hE _ he (by simp [h])
    have hcard : (E.erase s(a,b)).card = n := by
      rw [Finset.card_erase_of_mem he]; omega
    obtain ⟨c, hc⟩ := ih (E.erase s(a,b)) hcard (fun f hf => hE f (Finset.mem_of_mem_erase hf))
      (fun W hW => le_trans (Finset.card_le_card (Finset.filter_subset_filter _
        (Finset.erase_subset _ _))) (dens W hW))
    have main : ∀ m, ∀ c : Sym2 V → Fin (k+1), Valid (E.erase s(a,b)) c →
        (comp (cls (E.erase s(a,b)) c 0) a).card = m → ∃ c' : Sym2 V → Fin (k+1), Valid E c' := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ihm =>
        intro c hc hm
        rcases core_step E dens hab he c hc with h | ⟨c', hc', hlt⟩
        · exact h
        · exact ihm _ (hm ▸ hlt) c' hc' rfl
    exact main _ c hc rfl

end core

section glue
open Classical
variable [Fintype V]

lemma forest_card (S : Finset (Sym2 V)) (W : Finset V) (hW : W.Nonempty)
    (hnd : ∀ f ∈ S, ¬ f.IsDiag)
    (hS : ∀ f ∈ S, ∀ v ∈ f, v ∈ W) (hac : (fromEdgeSet (S : Set (Sym2 V))).IsAcyclic) :
    S.card + 1 ≤ W.card := by
  haveI : Nonempty W := ⟨⟨hW.choose, hW.choose_spec⟩⟩
  let G' : SimpleGraph W := (fromEdgeSet (S : Set (Sym2 V))).comap (Subtype.val : W → V)
  have hG' : G'.IsAcyclic := hac.of_comap (Function.Embedding.subtype _)
  obtain ⟨F, hF1, -, hF⟩ := (connected_top (V := W)).exists_isTree_le_of_le_of_isAcyclic
    (le_top : G' ≤ ⊤) hG'
  have h1 := hF.card_edgeFinset
  have h2 : S ⊆ (G'.edgeFinset).image (Sym2.map (Subtype.val : W → V)) := by
    intro f hf
    induction f using Sym2.ind with
    | h x y =>
      have hx : x ∈ W := hS _ hf x (Sym2.mem_mk_left _ _)
      have hy : y ∈ W := hS _ hf y (Sym2.mem_mk_right _ _)
      have hxy : x ≠ y := fun h => hnd _ hf (by simp [h])
      refine Finset.mem_image.mpr ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, by simp⟩
      simp [G', fromEdgeSet_adj, hf, hxy]
  have h3 := Finset.card_le_card h2
  have h4 := Finset.card_image_le (s := G'.edgeFinset) (f := Sym2.map (Subtype.val : W → V))
  have h5 : G'.edgeFinset.card ≤ F.edgeFinset.card :=
    Finset.card_le_card (by simpa using edgeSet_mono hF1)
  have h6 : Fintype.card W = W.card := by simp
  omega

lemma edges_le (E : Finset (Sym2 V)) (hE : ∀ f ∈ E, ¬ f.IsDiag) (W : Finset V) :
    (E.filter (fun f => ∀ v ∈ f, v ∈ W)).card ≤ W.card.choose 2 := by
  rw [← Sym2.card_image_offDiag]
  apply Finset.card_le_card
  intro f hf
  rw [Finset.mem_filter] at hf
  induction f using Sym2.ind with
  | h x y =>
    have hxy : x ≠ y := fun h => hE _ hf.1 (by simp [h])
    refine Finset.mem_image.mpr ⟨(x, y), ?_, rfl⟩
    simp [Finset.mem_offDiag, hf.2 x (Sym2.mem_mk_left _ _), hf.2 y (Sym2.mem_mk_right _ _), hxy]

end glue
end NW

namespace ConstructiveArboricity.Exact
open SimpleGraph NW
open Classical

noncomputable def Graph.edges (G : Graph) : Finset (Sym2 (Fin G.n)) :=
  Finset.univ.image G.edge

lemma Graph.edge_nd (G : Graph) (e : Fin G.m) : ¬ (G.edge e).IsDiag := by
  have := G.noLoops e
  simpa [Graph.edge] using this

lemma Graph.edges_nd (G : Graph) : ∀ f ∈ G.edges, ¬ f.IsDiag := by
  intro f hf
  obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hf
  exact G.edge_nd e

lemma Graph.mem_edges (G : Graph) {f : Sym2 (Fin G.n)} : f ∈ G.edges ↔ ∃ e, G.edge e = f := by
  simp [Graph.edges]

lemma Graph.graph_edgeSet (G : Graph) : G.graph.edgeSet = ↑G.edges := by
  ext f
  rw [Graph.graph, Graph.onEdges, edgeSet_fromEdgeSet]
  simp only [Set.mem_diff, Set.mem_image, Set.mem_univ, true_and, Finset.mem_coe, G.mem_edges]
  constructor
  · exact fun h => h.1
  · rintro ⟨e, rfl⟩; exact ⟨⟨e, rfl⟩, G.edge_nd e⟩

lemma Graph.eIn_eq (G : Graph) (W : Finset (Fin G.n)) :
    TaitTobin.Outerplanar.eIn G.graph W =
      (G.edges.filter (fun f => ∀ v ∈ f, v ∈ W)).card := by
  have h : G.graph.edgeFinset = G.edges := by
    ext f
    rw [mem_edgeFinset, G.graph_edgeSet, Finset.mem_coe]
  unfold TaitTobin.Outerplanar.eIn
  rw [h]
  apply congrArg Finset.card
  ext f
  simp only [Finset.mem_filter]

lemma Graph.rho_le (G : Graph) (k : ℕ)
    (h : ∀ W : Finset (Fin G.n), W.Nonempty →
      TaitTobin.Outerplanar.eIn G.graph W ≤ k * W.card) : G.rho ≤ k := by
  unfold Graph.rho SparseDisc.pseudoarboricity
  apply Finset.sup_le
  intro W _
  split_ifs with hW
  · have hpos : 0 < W.card := Finset.card_pos.mpr hW
    rw [Nat.div_le_iff_le_mul_add_pred hpos]
    have := h W hW
    rw [mul_comm] at this
    omega
  · exact Nat.zero_le _

lemma Graph.eIn_le_rho (G : Graph) (W : Finset (Fin G.n)) (hW : W.Nonempty) :
    TaitTobin.Outerplanar.eIn G.graph W ≤ G.rho * W.card := by
  have hpos : 0 < W.card := Finset.card_pos.mpr hW
  have h1 : (if W.Nonempty then (TaitTobin.Outerplanar.eIn G.graph W + W.card - 1) / W.card
      else 0) ≤ G.rho := by
    unfold Graph.rho SparseDisc.pseudoarboricity
    exact Finset.le_sup (f := fun W : Finset (Fin G.n) =>
      if W.Nonempty then (TaitTobin.Outerplanar.eIn G.graph W + W.card - 1) / W.card else 0)
      (Finset.mem_univ W)
  rw [if_pos hW, Nat.div_le_iff_le_mul_add_pred hpos] at h1
  rw [mul_comm]
  omega

lemma Graph.feasible_rho (G : Graph) : G.Feasible (G.rho + 1) := by
  have hdens : ∀ W : Finset (Fin G.n), W.Nonempty →
      (G.edges.filter (fun f => ∀ v ∈ f, v ∈ W)).card ≤ (G.rho + 1) * (W.card - 1) := by
    intro W hW
    have hpos : 0 < W.card := Finset.card_pos.mpr hW
    by_cases hc : G.rho + 1 ≤ W.card
    · have := G.eIn_le_rho W hW
      rw [G.eIn_eq] at this
      obtain ⟨t, ht⟩ : ∃ t, W.card = G.rho + 1 + t := ⟨W.card - (G.rho + 1), by omega⟩
      rw [ht] at this ⊢
      have : (G.rho + 1) * (G.rho + 1 + t - 1) = G.rho * (G.rho + 1 + t) + t := by
        rw [show G.rho + 1 + t - 1 = G.rho + t by omega]; ring
      omega
    · have h1 := edges_le G.edges G.edges_nd W
      rw [Nat.choose_two_right] at h1
      obtain ⟨t, ht⟩ : ∃ t, W.card = t + 1 := ⟨W.card - 1, by omega⟩
      have h2 : W.card * (W.card - 1) / 2 ≤ (G.rho + 1) * (W.card - 1) := by
        apply Nat.div_le_of_le_mul
        rw [ht] at hc ⊢
        simp only [Nat.add_sub_cancel]
        nlinarith
      refine Nat.le_trans ?_ h2
      convert h1 using 2
      ext f
      simp only [Finset.mem_filter]
  obtain ⟨c, hc⟩ := nash_williams (k := G.rho) _ G.edges rfl G.edges_nd (fun W hW => by convert hdens W hW)
  refine ⟨fun e => c (G.edge e), fun i => ?_⟩
  unfold Graph.IsForest Graph.onEdges
  have : G.edge '' {e | c (G.edge e) = i} = cls G.edges c i := by
    ext f
    simp only [cls, Set.mem_setOf_eq, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨e, he, rfl⟩; exact ⟨G.mem_edges.mpr ⟨e, rfl⟩, he⟩
    · rintro ⟨hf, he⟩
      obtain ⟨e, rfl⟩ := G.mem_edges.mp hf
      exact ⟨e, he, rfl⟩
  rw [this]
  exact hc i

lemma Graph.rho_le_of_feasible (G : Graph) (k : ℕ) (hf : G.Feasible k) : G.rho ≤ k := by
  obtain ⟨c, hc⟩ := hf
  apply G.rho_le
  intro W hW
  rw [G.eIn_eq]
  let Fm : Finset (Fin G.m) := Finset.univ.filter
    (fun e => (G.ends e).1 ∈ W ∧ (G.ends e).2 ∈ W)
  have h1 : G.edges.filter (fun f => ∀ v ∈ f, v ∈ W) = Fm.image G.edge := by
    ext f
    simp only [Finset.mem_filter, Graph.edges, Finset.mem_image, Finset.mem_univ, true_and, Fm]
    constructor
    · rintro ⟨⟨e, rfl⟩, h⟩
      exact ⟨e, ⟨h _ (Sym2.mem_mk_left _ _), h _ (Sym2.mem_mk_right _ _)⟩, rfl⟩
    · rintro ⟨e, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨e, rfl⟩, fun v hv => ?_⟩
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact h1
      · exact h2
  have hinj : Function.Injective G.edge := G.simple
  rw [h1, Finset.card_image_of_injective _ hinj,
    Finset.card_eq_sum_card_fiberwise (f := c) (t := Finset.univ) (fun x _ => Finset.mem_univ _)]
  calc ∑ i : Fin k, (Fm.filter (fun e => c e = i)).card ≤ ∑ _i : Fin k, W.card := by
        apply Finset.sum_le_sum
        intro i _
        have hac : (fromEdgeSet (((Fm.filter (fun e => c e = i)).image G.edge : Finset _) :
            Set (Sym2 (Fin G.n)))).IsAcyclic := by
          refine (hc i).anti (fromEdgeSet_mono ?_)
          intro f hf
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_filter] at hf
          obtain ⟨e, ⟨_, he⟩, rfl⟩ := hf
          exact ⟨e, he, rfl⟩
        have := forest_card ((Fm.filter (fun e => c e = i)).image G.edge) W hW
          (by
            intro f hf
            obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hf
            exact G.edge_nd e)
          (by
            intro f hf v hv
            obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hf
            simp only [Finset.mem_filter, Fm, Finset.mem_univ, true_and] at he
            rcases Sym2.mem_iff.mp hv with rfl | rfl
            · exact he.1.1
            · exact he.1.2) hac
        rw [Finset.card_image_of_injective _ hinj] at this
        omega
    _ = k * W.card := by simp

end ConstructiveArboricity.Exact

theorem solution (G : ConstructiveArboricity.Exact.Graph) :
    G.rho ≤ G.arboricity ∧ G.arboricity ≤ G.rho + 1 := by
  open ConstructiveArboricity.Exact in
  have hne : {k | G.Feasible k}.Nonempty := ⟨G.rho + 1, G.feasible_rho⟩
  refine ⟨?_, Nat.sInf_le G.feasible_rho⟩
  exact G.rho_le_of_feasible _ (Nat.sInf_mem hne)
