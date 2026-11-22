-- Prove2me | solution 1 for CoDecompFO.lemma_B_2
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:42:11.064934+00:00
-- url     : https://prove2.me/submissions/db6124e3-a8d1-473d-b75a-58dd5d948d40

import Mathlib
import Definitions.Def_CoDecompFO_Lim
import Definitions.Def_CoDecompFO_HTh

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

namespace TreeAux

open SimpleGraph

section Graph

variable {V : Type} {G : SimpleGraph V}

/-- A step along a geodesic. -/
theorem exists_adj_dist (hG : G.Connected) {u c : V} (h : u ≠ c) :
    ∃ u', G.Adj u u' ∧ G.dist u' c + 1 = G.dist u c := by
  obtain ⟨p, -, hlen⟩ := hG.exists_path_of_dist u c
  cases p with
  | nil => exact absurd rfl h
  | @cons _ w _ hadj q =>
    refine ⟨w, hadj, ?_⟩
    have h1 : G.dist w c ≤ q.length := dist_le q
    have h2 : G.dist u c ≤ G.dist u w + G.dist w c := hG.dist_triangle
    have h3 : G.dist u w = 1 := dist_eq_one_iff_adj.2 hadj
    rw [Walk.length_cons] at hlen
    omega

/-- In a tree, a vertex has at most one neighbour that is closer to the root. -/
theorem parent_unique (hG : G.IsTree) {r v w₁ w₂ : V} (h₁ : G.Adj v w₁) (h₂ : G.Adj v w₂)
    (d₁ : G.dist w₁ r + 1 = G.dist v r) (d₂ : G.dist w₂ r + 1 = G.dist v r) : w₁ = w₂ := by
  classical
  obtain ⟨p₁, hp₁, l₁⟩ := hG.connected.exists_path_of_dist w₁ r
  obtain ⟨p₂, hp₂, l₂⟩ := hG.connected.exists_path_of_dist w₂ r
  have n₁ : v ∉ p₁.support := by
    intro hv
    have a1 := dist_le (p₁.dropUntil v hv)
    have a2 := p₁.length_dropUntil_le_length hv
    omega
  have n₂ : v ∉ p₂.support := by
    intro hv
    have a1 := dist_le (p₂.dropUntil v hv)
    have a2 := p₂.length_dropUntil_le_length hv
    omega
  have e := (hG.isAcyclic.subsingleton_path v r).elim
    ⟨Walk.cons h₁ p₁, hp₁.cons n₁⟩ ⟨Walk.cons h₂ p₂, hp₂.cons n₂⟩
  have e' : Walk.cons h₁ p₁ = Walk.cons h₂ p₂ := congrArg Subtype.val e
  have e'' := congrArg Walk.snd e'
  simpa using e''

/-- In a tree, an edge that leaves the set of vertices below `c` starts at `c` and ends at the
neighbour of `c` that is closer to the root. -/
theorem cross (hG : G.IsTree) {r c u v : V} (huv : G.Adj u v)
    (hu : G.dist u r = G.dist u c + G.dist c r) (hv : G.dist v r ≠ G.dist v c + G.dist c r) :
    u = c ∧ G.dist v r + 1 = G.dist c r := by
  have hc := hG.connected
  have t1 : G.dist v r ≤ G.dist v c + G.dist c r := hc.dist_triangle
  have t2 : G.dist v c ≤ G.dist v u + G.dist u c := hc.dist_triangle
  have t3 : G.dist v u = 1 := dist_eq_one_iff_adj.2 huv.symm
  have a1 : G.dist u r = G.dist v r + 1 ∨ G.dist v r = G.dist u r + 1 := by
    have := hG.dist_eq_dist_add_one_of_adj r huv
    rw [dist_comm (u := r) (v := u), dist_comm (u := r) (v := v)] at this
    exact this
  have a2 : G.dist u c = G.dist v c + 1 ∨ G.dist v c = G.dist u c + 1 := by
    have := hG.dist_eq_dist_add_one_of_adj c huv
    rw [dist_comm (u := c) (v := u), dist_comm (u := c) (v := v)] at this
    exact this
  have b1 : G.dist u r = G.dist v r + 1 := by omega
  have b2 : G.dist v c = G.dist u c + 1 := by omega
  have huc : u = c := by
    by_contra hne
    obtain ⟨u', hadj, hd⟩ := exists_adj_dist hc hne
    have t4 : G.dist u' r ≤ G.dist u' c + G.dist c r := hc.dist_triangle
    have t5 : G.dist u r ≤ G.dist u u' + G.dist u' r := hc.dist_triangle
    have t6 : G.dist u u' = 1 := dist_eq_one_iff_adj.2 hadj
    have hp : u' = v := parent_unique hG (r := r) hadj huv (by omega) (by omega)
    subst hp
    omega
  subst huc
  exact ⟨rfl, by omega⟩

end Graph

variable {σ : Sig}

theorem graph_isTree (T : CoDecomp σ) : T.graph.IsTree := T.isTree

theorem graph_adj (T : CoDecomp σ) (e : Fin T.m) : T.graph.Adj (T.ends e).1 (T.ends e).2 := by
  rw [CoDecomp.graph, fromEdgeSet_adj]
  exact ⟨⟨e, rfl⟩, T.ends_ne e⟩

theorem exists_edge_of_adj (T : CoDecomp σ) {u v : Fin T.b} (h : T.graph.Adj u v) :
    ∃ e, ((T.ends e).1 = u ∧ (T.ends e).2 = v) ∨ ((T.ends e).1 = v ∧ (T.ends e).2 = u) := by
  rw [CoDecomp.graph, fromEdgeSet_adj] at h
  obtain ⟨⟨e, he⟩, -⟩ := h
  exact ⟨e, Sym2.eq_iff.1 he⟩

theorem edge_unique (T : CoDecomp σ) {e e' : Fin T.m}
    (h : ((T.ends e).1 = (T.ends e').1 ∧ (T.ends e).2 = (T.ends e').2) ∨
      ((T.ends e).1 = (T.ends e').2 ∧ (T.ends e).2 = (T.ends e').1)) : e = e' :=
  T.ends_inj (Sym2.eq_iff.2 h)

theorem child_spec (T : CoDecomp σ) {r t : Fin T.b} {e : Fin T.m} (he : T.IsChildEdge r t e) :
    (((T.ends e).1 = t ∧ (T.ends e).2 = T.child e t) ∨
      ((T.ends e).2 = t ∧ (T.ends e).1 = T.child e t)) ∧
    T.graph.dist (T.child e t) r = T.graph.dist t r + 1 := by
  rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hc : T.child e t = (T.ends e).2 := by
      unfold CoDecomp.child
      rw [if_pos h1]
    rw [hc]
    exact ⟨Or.inl ⟨h1, rfl⟩, h2⟩
  · have hne : (T.ends e).1 ≠ t := fun h => T.ends_ne e (h.trans h1.symm)
    have hc : T.child e t = (T.ends e).1 := by
      unfold CoDecomp.child
      rw [if_neg hne]
    rw [hc]
    exact ⟨Or.inr ⟨h1, rfl⟩, h2⟩

theorem dist_child (T : CoDecomp σ) {r t : Fin T.b} {e : Fin T.m} (he : T.IsChildEdge r t e) :
    T.graph.dist (T.child e t) r = T.graph.dist t r + 1 := (child_spec T he).2

theorem adj_child (T : CoDecomp σ) {r t : Fin T.b} {e : Fin T.m} (he : T.IsChildEdge r t e) :
    T.graph.Adj t (T.child e t) := by
  have h := graph_adj T e
  rcases (child_spec T he).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2] at h
    exact h
  · rw [h1, h2] at h
    exact h.symm

theorem subtree_child_subset (T : CoDecomp σ) {r t : Fin T.b} {e : Fin T.m}
    (he : T.IsChildEdge r t e) : T.subtree r (T.child e t) ⊆ T.subtree r t := by
  intro s hs
  have hs' : T.graph.dist s r = T.graph.dist s (T.child e t) + T.graph.dist (T.child e t) r := hs
  show T.graph.dist s r = T.graph.dist s t + T.graph.dist t r
  have hc := (graph_isTree T).connected
  have h1 : T.graph.dist s r ≤ T.graph.dist s t + T.graph.dist t r := hc.dist_triangle
  have h2 : T.graph.dist s t ≤ T.graph.dist s (T.child e t) + T.graph.dist (T.child e t) t :=
    hc.dist_triangle
  have h3 : T.graph.dist (T.child e t) t = 1 := dist_eq_one_iff_adj.2 (adj_child T he).symm
  have h4 := dist_child T he
  omega

theorem not_mem_subtree_child (T : CoDecomp σ) {r t : Fin T.b} {e : Fin T.m}
    (he : T.IsChildEdge r t e) : t ∉ T.subtree r (T.child e t) := by
  intro hs
  have hs' : T.graph.dist t r = T.graph.dist t (T.child e t) + T.graph.dist (T.child e t) r := hs
  have h3 : T.graph.dist t (T.child e t) = 1 := dist_eq_one_iff_adj.2 (adj_child T he)
  have h4 := dist_child T he
  omega

/-- An edge that leaves the subtree of a child `c` of `t` joins `c` to `t`. -/
theorem cross_child (T : CoDecomp σ) {r t : Fin T.b} {e : Fin T.m} (he : T.IsChildEdge r t e)
    {u v : Fin T.b} (huv : T.graph.Adj u v) (hu : u ∈ T.subtree r (T.child e t))
    (hv : v ∉ T.subtree r (T.child e t)) : u = T.child e t ∧ v = t := by
  obtain ⟨h1, h2⟩ := cross (graph_isTree T) huv hu hv
  refine ⟨h1, ?_⟩
  subst h1
  exact parent_unique (graph_isTree T) (r := r) huv (adj_child T he).symm h2 (by rw [dist_child T he])

/-- A crossing edge is the child edge itself. -/
theorem cross_edge (T : CoDecomp σ) {r t : Fin T.b} {e e' : Fin T.m} (he : T.IsChildEdge r t e)
    (h : ((T.ends e').1 = T.child e t ∧ (T.ends e').2 = t) ∨
      ((T.ends e').2 = T.child e t ∧ (T.ends e').1 = t)) : e' = e := by
  apply edge_unique
  rcases h with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases (child_spec T he).1 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · right; exact ⟨a1.trans b2.symm, a2.trans b1.symm⟩
  · left; exact ⟨a1.trans b2.symm, a2.trans b1.symm⟩
  · left; exact ⟨a2.trans b1.symm, a1.trans b2.symm⟩
  · right; exact ⟨a2.trans b1.symm, a1.trans b2.symm⟩

theorem exists_child_of_mem (T : CoDecomp σ) {r t s : Fin T.b} (hs : s ∈ T.subtree r t)
    (hne : s ≠ t) : ∃ e, T.IsChildEdge r t e ∧ s ∈ T.subtree r (T.child e t) := by
  have hc := (graph_isTree T).connected
  obtain ⟨c, hadj, hd⟩ := exists_adj_dist hc (u := t) (c := s) (Ne.symm hne)
  have hs' : T.graph.dist s r = T.graph.dist s t + T.graph.dist t r := hs
  have h1 : T.graph.dist c r ≤ T.graph.dist c t + T.graph.dist t r := hc.dist_triangle
  have h2 : T.graph.dist c t = 1 := dist_eq_one_iff_adj.2 hadj.symm
  have h3 : T.graph.dist s r ≤ T.graph.dist s c + T.graph.dist c r := hc.dist_triangle
  have h4 : T.graph.dist s c = T.graph.dist c s := dist_comm
  have h5 : T.graph.dist s t = T.graph.dist t s := dist_comm
  have hcr : T.graph.dist c r = T.graph.dist t r + 1 := by omega
  have hsc : T.graph.dist s r = T.graph.dist s c + T.graph.dist c r := by omega
  obtain ⟨e, he⟩ := exists_edge_of_adj T hadj
  rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · have hce : T.IsChildEdge r t e := Or.inl ⟨e1, by rw [e2]; exact hcr⟩
    have hch : T.child e t = c := by
      rcases (child_spec T hce).1 with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · exact b2.symm.trans e2
      · exact absurd (b1.symm.trans e2) hadj.ne
    exact ⟨e, hce, by rw [hch]; exact hsc⟩
  · have hce : T.IsChildEdge r t e := Or.inr ⟨e2, by rw [e1]; exact hcr⟩
    have hch : T.child e t = c := by
      rcases (child_spec T hce).1 with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · exact absurd (b1.symm.trans e1) hadj.ne
      · exact b2.symm.trans e1
    exact ⟨e, hce, by rw [hch]; exact hsc⟩

theorem child_edge_unique (T : CoDecomp σ) {r t s : Fin T.b} {e e' : Fin T.m}
    (he : T.IsChildEdge r t e) (he' : T.IsChildEdge r t e')
    (hs : s ∈ T.subtree r (T.child e t)) (hs' : s ∈ T.subtree r (T.child e' t)) : e = e' := by
  have key : ∀ {e : Fin T.m}, T.IsChildEdge r t e → s ∈ T.subtree r (T.child e t) →
      T.graph.dist (T.child e t) s + 1 = T.graph.dist t s := by
    intro e he hs
    have hs1 : T.graph.dist s r = T.graph.dist s (T.child e t) + T.graph.dist (T.child e t) r := hs
    have hs2 : T.graph.dist s r = T.graph.dist s t + T.graph.dist t r :=
      subtree_child_subset T he hs
    have h3 := dist_child T he
    have h4 : T.graph.dist s (T.child e t) = T.graph.dist (T.child e t) s := dist_comm
    have h5 : T.graph.dist s t = T.graph.dist t s := dist_comm
    omega
  have hcc : T.child e t = T.child e' t :=
    parent_unique (graph_isTree T) (r := s) (adj_child T he) (adj_child T he') (key he hs) (key he' hs')
  apply edge_unique
  rcases (child_spec T he).1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
    rcases (child_spec T he').1 with ⟨b1, b2⟩ | ⟨b1, b2⟩
  · left; exact ⟨a1.trans b1.symm, a2.trans (hcc.trans b2.symm)⟩
  · right; exact ⟨a1.trans b1.symm, a2.trans (hcc.trans b2.symm)⟩
  · right; exact ⟨a2.trans (hcc.trans b2.symm), a1.trans b1.symm⟩
  · left; exact ⟨a2.trans (hcc.trans b2.symm), a1.trans b1.symm⟩

/-- Restriction of a matching family to a smaller set of nodes. -/
def restrict (T : CoDecomp σ) {S₁ S₂ : Set (Fin T.b)} (h : S₂ ⊆ S₁) (x : T.LimOn S₁) :
    T.LimOn S₂ :=
  ⟨fun s => x.val ⟨s.1, h s.2⟩, fun e h₁ h₂ => x.compat e (h h₁) (h h₂)⟩

theorem edgeMap_val_fst (T : CoDecomp σ) {S : Set (Fin T.b)} (y : T.LimOn S) (e : Fin T.m)
    (s : Fin T.b) (hs : s = (T.ends e).1 ∨ s = (T.ends e).2) (m : s ∈ S)
    (h : s = (T.ends e).1) (m' : (T.ends e).1 ∈ S) :
    T.edgeMap e s hs (y.val ⟨s, m⟩) = T.gl e (y.val ⟨(T.ends e).1, m'⟩) := by
  subst h
  unfold CoDecomp.edgeMap
  rw [dif_pos rfl]

theorem edgeMap_val_snd (T : CoDecomp σ) {S : Set (Fin T.b)} (y : T.LimOn S) (e : Fin T.m)
    (s : Fin T.b) (hs : s = (T.ends e).1 ∨ s = (T.ends e).2) (m : s ∈ S)
    (h : s = (T.ends e).2) (m' : (T.ends e).2 ∈ S) :
    T.edgeMap e s hs (y.val ⟨s, m⟩) = T.gr e (y.val ⟨(T.ends e).2, m'⟩) := by
  subst h
  unfold CoDecomp.edgeMap
  rw [dif_neg (fun h => T.ends_ne e h.symm)]

/-- Agreement on an adhesion, in the symmetric form. -/
theorem edgeMap_compat (T : CoDecomp σ) {S : Set (Fin T.b)} (x : T.LimOn S) (e : Fin T.m)
    (s₁ s₂ : Fin T.b) (hs₁ : s₁ = (T.ends e).1 ∨ s₁ = (T.ends e).2)
    (hs₂ : s₂ = (T.ends e).1 ∨ s₂ = (T.ends e).2) (m₁ : s₁ ∈ S) (m₂ : s₂ ∈ S) (hne : s₁ ≠ s₂) :
    T.edgeMap e s₁ hs₁ (x.val ⟨s₁, m₁⟩) = T.edgeMap e s₂ hs₂ (x.val ⟨s₂, m₂⟩) := by
  have k₁ := hs₁
  have k₂ := hs₂
  rcases k₁ with h | h <;> rcases k₂ with h' | h'
  · exact absurd (h.trans h'.symm) hne
  · rw [edgeMap_val_fst T x e s₁ hs₁ m₁ h (h ▸ m₁), edgeMap_val_snd T x e s₂ hs₂ m₂ h' (h' ▸ m₂)]
    exact x.compat e _ _
  · rw [edgeMap_val_snd T x e s₁ hs₁ m₁ h (h ▸ m₁), edgeMap_val_fst T x e s₂ hs₂ m₂ h' (h' ▸ m₂)]
    exact (x.compat e _ _).symm
  · exact absurd (h.trans h'.symm) hne

end TreeAux

end CoDecompFO

namespace CoDecompFO

open FirstOrder

namespace B2

open TreeAux SimpleGraph

variable {σ : Sig}

/-- A bijection that preserves and reflects the relations is an isomorphism of `σ`-structures. -/
noncomputable def mkEquiv {M N : Type} [σ.lang.Structure M] [σ.lang.Structure N] (f : M → N)
    (hb : Function.Bijective f)
    (hf : ∀ (i : Fin σ.r) (args : Fin (σ.ar i) → M), σ.holds i (f ∘ args) ↔ σ.holds i args) :
    M ≃[σ.lang] N :=
  { Equiv.ofBijective f hb with
    map_fun' := fun {_} F _ => (show Empty from F).elim
    map_rel' := fun {_} R x => by
      obtain ⟨i, rfl⟩ := R
      exact hf i x }

/-- The identification of the points of two equal bags is a homomorphism. -/
theorem castHom {B B' : Bag σ} (h : B = B') : IsHom σ (Fin.cast (congrArg Bag.n h)) := by
  subst h
  intro i args hh
  exact hh

theorem cast_bij {n m : ℕ} (h : n = m) : Function.Bijective (Fin.cast h) :=
  (finCongr h).bijective

/-! ### Co-decompositions indexed by arbitrary types -/

/-- A tree co-decomposition whose nodes and edges are indexed by arbitrary types. -/
structure GCD (σ : Sig) (V E : Type) where
  bag : V → Bag σ
  ends : E → V × V
  ends_ne : ∀ e, (ends e).1 ≠ (ends e).2
  ends_inj : Function.Injective (fun e => s((ends e).1, (ends e).2))
  isTree : (SimpleGraph.fromEdgeSet (Set.range fun e => s((ends e).1, (ends e).2))).IsTree
  adh : E → Bag σ
  gl : (e : E) → Fin (bag (ends e).1).n → Fin (adh e).n
  gr : (e : E) → Fin (bag (ends e).2).n → Fin (adh e).n
  gl_surj : ∀ e, Function.Surjective (gl e)
  gr_surj : ∀ e, Function.Surjective (gr e)
  gl_hom : ∀ e, IsHom σ (gl e)
  gr_hom : ∀ e, IsHom σ (gr e)

variable {V E : Type} (D : GCD σ V E) {b m : ℕ} (eV : V ≃ Fin b) (eE : E ≃ Fin m)

theorem bag_symm (v : V) : D.bag (eV.symm (eV v)) = D.bag v :=
  congrArg D.bag (eV.symm_apply_apply v)

/-- The graph of the re-indexed co-decomposition is isomorphic to the original graph. -/
def graphIso :
    SimpleGraph.fromEdgeSet (Set.range fun e => s((D.ends e).1, (D.ends e).2)) ≃g
      SimpleGraph.fromEdgeSet (Set.range fun e : Fin m =>
        s(eV (D.ends (eE.symm e)).1, eV (D.ends (eE.symm e)).2)) where
  toEquiv := eV
  map_rel_iff' := by
    intro a c
    rw [fromEdgeSet_adj, fromEdgeSet_adj]
    constructor
    · rintro ⟨⟨e, he⟩, hne⟩
      have he' : Sym2.map eV s((D.ends (eE.symm e)).1, (D.ends (eE.symm e)).2) =
          Sym2.map eV s(a, c) := he
      exact ⟨⟨eE.symm e, Sym2.map.injective eV.injective he'⟩, fun h => hne (congrArg eV h)⟩
    · rintro ⟨⟨e', he'⟩, hne⟩
      refine ⟨⟨eE e', ?_⟩, fun h => hne (eV.injective h)⟩
      have h1 : eE.symm (eE e') = e' := eE.symm_apply_apply e'
      show s(eV (D.ends (eE.symm (eE e'))).1, eV (D.ends (eE.symm (eE e'))).2) = s(eV a, eV c)
      rw [h1]
      exact congrArg (Sym2.map eV) he'

/-- Re-indexing by `Fin`. -/
noncomputable def GCD.toCoDecomp : CoDecomp σ where
  b := b
  bag := fun i => D.bag (eV.symm i)
  m := m
  ends := fun e => (eV (D.ends (eE.symm e)).1, eV (D.ends (eE.symm e)).2)
  ends_ne := fun e h => D.ends_ne _ (eV.injective h)
  ends_inj := by
    intro e e' h
    have h' : Sym2.map eV s((D.ends (eE.symm e)).1, (D.ends (eE.symm e)).2) =
        Sym2.map eV s((D.ends (eE.symm e')).1, (D.ends (eE.symm e')).2) := h
    exact eE.symm.injective (D.ends_inj (Sym2.map.injective eV.injective h'))
  isTree := (graphIso D eV eE).isTree_iff.1 D.isTree
  adh := fun e => D.adh (eE.symm e)
  gl := fun e x => D.gl (eE.symm e) (Fin.cast (congrArg Bag.n (bag_symm D eV _)) x)
  gr := fun e x => D.gr (eE.symm e) (Fin.cast (congrArg Bag.n (bag_symm D eV _)) x)
  gl_surj := fun e => (D.gl_surj _).comp (cast_bij _).2
  gr_surj := fun e => (D.gr_surj _).comp (cast_bij _).2
  gl_hom := fun e i args hh => D.gl_hom _ i _ (castHom (bag_symm D eV _) i args hh)
  gr_hom := fun e i args hh => D.gr_hom _ i _ (castHom (bag_symm D eV _) i args hh)

/-- The matching families of an indexed co-decomposition. -/
def GCD.Lim (D : GCD σ V E) : Type :=
  {y : (v : V) → Fin (D.bag v).n // ∀ e, D.gl e (y (D.ends e).1) = D.gr e (y (D.ends e).2)}

instance GCD.Lim.structure (D : GCD σ V E) : σ.lang.Structure D.Lim :=
  σ.structureOf (fun i args => ∀ v, σ.holds i (fun j => (args j).1 v))

theorem cast_val (y : (v : V) → Fin (D.bag v).n) (v' v : V) (h : v' = v)
    (hn : (D.bag v').n = (D.bag v).n) : Fin.cast hn (y v') = y v := by
  subst h
  rfl

/-- A matching family, re-indexed. -/
noncomputable def GCD.toLim (y : D.Lim) : (D.toCoDecomp eV eE).Lim :=
  ⟨fun i => y.1 (eV.symm i), fun e =>
    (congrArg (D.gl (eE.symm e)) (cast_val D y.1 _ _ (eV.symm_apply_apply _) _)).trans
      ((y.2 (eE.symm e)).trans
        (congrArg (D.gr (eE.symm e)) (cast_val D y.1 _ _ (eV.symm_apply_apply _) _)).symm)⟩

theorem toLim_inj : Function.Injective (D.toLim eV eE) := by
  intro y y' h
  apply Subtype.ext
  funext v
  exact (eV.symm.surjective.forall (p := fun v => y.1 v = y'.1 v)).2
    (fun i => congrFun (congrArg CoDecomp.Lim.val h) i) v

theorem cast_val' (x : (D.toCoDecomp eV eE).Lim) (i' i : Fin b) (h : i' = i)
    (hn : (D.bag (eV.symm i')).n = (D.bag (eV.symm i)).n) :
    Fin.cast hn (x.val i') = x.val i := by
  subst h
  rfl

theorem toLim_surj : Function.Surjective (D.toLim eV eE) := by
  intro x
  refine ⟨⟨fun v => Fin.cast (congrArg Bag.n (bag_symm D eV v)) (x.val (eV v)), ?_⟩, ?_⟩
  · exact (eE.symm.surjective.forall (p := fun e' =>
      D.gl e' (Fin.cast (congrArg Bag.n (bag_symm D eV (D.ends e').1)) (x.val (eV (D.ends e').1))) =
        D.gr e' (Fin.cast (congrArg Bag.n (bag_symm D eV (D.ends e').2))
          (x.val (eV (D.ends e').2))))).2 (fun e => x.compat e)
  · apply CoDecomp.Lim.ext
    funext i
    exact cast_val' D eV eE x _ _ (eV.apply_symm_apply i)
      (congrArg Bag.n (bag_symm D eV (eV.symm i)))

theorem toLim_holds (i : Fin σ.r) (args : Fin (σ.ar i) → D.Lim) :
    σ.holds i (D.toLim eV eE ∘ args) ↔ σ.holds i args := by
  show (∀ t : Fin b, σ.holds i (fun j => (args j).1 (eV.symm t))) ↔
    (∀ v, σ.holds i (fun j => (args j).1 v))
  exact (eV.symm.surjective.forall (p := fun v => σ.holds i (fun j => (args j).1 v))).symm

/-! ### Incident edges and child edges -/

/-- The edges at a node. -/
def inc (T : CoDecomp σ) (t : Fin T.b) : Set (Fin T.m) := {e | (T.ends e).1 = t ∨ (T.ends e).2 = t}

/-- The edges at a node of an indexed co-decomposition. -/
def GCD.inc (D : GCD σ V E) (v : V) : Set E := {e | (D.ends e).1 = v ∨ (D.ends e).2 = v}

theorem child_subset_inc (T : CoDecomp σ) (r t : Fin T.b) :
    {e | T.IsChildEdge r t e} ⊆ inc T t := by
  intro e he
  rcases he with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Away from the root, one of the edges at a node is not a child edge. -/
theorem child_ncard_lt (T : CoDecomp σ) {r t : Fin T.b} (h : t ≠ r) :
    {e | T.IsChildEdge r t e}.ncard < (inc T t).ncard := by
  refine Set.ncard_lt_ncard ⟨child_subset_inc T r t, ?_⟩ (Set.toFinite _)
  intro hsub
  obtain ⟨t', hadj, hd⟩ := exists_adj_dist (graph_isTree T).connected h
  obtain ⟨e, he⟩ := exists_edge_of_adj T hadj
  have hin : e ∈ inc T t := by
    rcases he with ⟨a, -⟩ | ⟨-, a⟩
    · exact Or.inl a
    · exact Or.inr a
  have hch : T.IsChildEdge r t e := hsub hin
  rcases hch with ⟨c1, c2⟩ | ⟨c1, c2⟩ <;> rcases he with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · rw [a2] at c2
    omega
  · rw [a2] at c2
    omega
  · rw [a1] at c2
    omega
  · rw [a1] at c2
    omega

theorem inc_toCoDecomp (i : Fin b) :
    inc (D.toCoDecomp eV eE) i = eE '' D.inc (eV.symm i) := by
  ext e
  constructor
  · intro h
    refine ⟨eE.symm e, ?_, eE.apply_symm_apply e⟩
    rcases h with h | h
    · exact Or.inl (eV.eq_symm_apply.2 h)
    · exact Or.inr (eV.eq_symm_apply.2 h)
  · rintro ⟨e', h, rfl⟩
    have h1 : eE.symm (eE e') = e' := eE.symm_apply_apply e'
    show eV (D.ends (eE.symm (eE e'))).1 = i ∨ eV (D.ends (eE.symm (eE e'))).2 = i
    rw [h1]
    rcases h with h | h
    · exact Or.inl (eV.eq_symm_apply.1 h)
    · exact Or.inr (eV.eq_symm_apply.1 h)

/-- The number of child edges at a node, bounded through the edges at the node. -/
theorem child_ncard_le (rs i : Fin b)
    (h : (D.inc (eV.symm i)).ncard ≤ 2 ∨ (i ≠ rs ∧ (D.inc (eV.symm i)).ncard ≤ 3)) :
    {e | (D.toCoDecomp eV eE).IsChildEdge rs i e}.ncard ≤ 2 := by
  have h1 : (inc (D.toCoDecomp eV eE) i).ncard = (D.inc (eV.symm i)).ncard := by
    rw [inc_toCoDecomp]
    exact Set.ncard_image_of_injective _ eE.injective
  rcases h with h | ⟨hne, h⟩
  · exact (Set.ncard_le_ncard (child_subset_inc (D.toCoDecomp eV eE) rs i)
      (Set.toFinite _)).trans (h1.le.trans h)
  · have h2 := child_ncard_lt (D.toCoDecomp eV eE) hne
    omega

end B2

end CoDecompFO

namespace CoDecompFO

open FirstOrder

namespace B2

open TreeAux SimpleGraph

variable {σ : Sig}

/-! ### General facts -/

theorem edgeMap_surj (T : CoDecomp σ) (e : Fin T.m) (s : Fin T.b)
    (hs : s = (T.ends e).1 ∨ s = (T.ends e).2) : Function.Surjective (T.edgeMap e s hs) := by
  by_cases h : s = (T.ends e).1
  · subst h
    intro y
    obtain ⟨x, hx⟩ := T.gl_surj e y
    refine ⟨x, ?_⟩
    unfold CoDecomp.edgeMap
    rw [dif_pos rfl]
    exact hx
  · have h2 : s = (T.ends e).2 := hs.resolve_left h
    subst h2
    intro y
    obtain ⟨x, hx⟩ := T.gr_surj e y
    refine ⟨x, ?_⟩
    unfold CoDecomp.edgeMap
    rw [dif_neg h]
    exact hx

theorem edgeMap_hom (T : CoDecomp σ) (e : Fin T.m) (s : Fin T.b)
    (hs : s = (T.ends e).1 ∨ s = (T.ends e).2) : IsHom σ (T.edgeMap e s hs) := by
  by_cases h : s = (T.ends e).1
  · subst h
    have e1 : T.edgeMap e (T.ends e).1 hs = T.gl e := by
      funext x
      unfold CoDecomp.edgeMap
      rw [dif_pos rfl]
    rw [e1]
    exact T.gl_hom e
  · have h2 : s = (T.ends e).2 := hs.resolve_left h
    subst h2
    have e1 : T.edgeMap e (T.ends e).2 hs = T.gr e := by
      funext x
      unfold CoDecomp.edgeMap
      rw [dif_neg h]
    rw [e1]
    exact T.gr_hom e

/-- The number of edges of a graph given by an injective list of non-loops. -/
theorem card_edgeSet {V E : Type} (ends : E → V × V) (hne : ∀ e, (ends e).1 ≠ (ends e).2)
    (hinj : Function.Injective (fun e => s((ends e).1, (ends e).2))) :
    Nat.card (SimpleGraph.fromEdgeSet (Set.range fun e => s((ends e).1, (ends e).2))).edgeSet =
      Nat.card E := by
  rw [edgeSet_fromEdgeSet]
  have h1 : Set.range (fun e => s((ends e).1, (ends e).2)) \ Sym2.diagSet =
      Set.range (fun e => s((ends e).1, (ends e).2)) := by
    ext z
    constructor
    · exact fun h => h.1
    · rintro ⟨e, rfl⟩
      exact ⟨⟨e, rfl⟩, fun h => hne e (Sym2.mk_isDiag_iff.1 h)⟩
  rw [h1]
  exact (Nat.card_congr (Equiv.ofInjective _ hinj)).symm

/-- A tree with `b` nodes has `b - 1` edges. -/
theorem edges_add_one (T : CoDecomp σ) : T.m + 1 = T.b := by
  have h := (isTree_iff_connected_and_card.1 (graph_isTree T)).2
  have h2 := card_edgeSet T.ends T.ends_ne T.ends_inj
  have h3 : Nat.card (T.graph.edgeSet) = T.m := by
    rw [CoDecomp.graph, h2]
    simp
  rw [h3] at h
  simpa using h

/-! ### Parents, children and the chain of siblings -/

variable (T : CoDecomp σ) (r : Fin T.b)

/-- The end of `e` that is closer to the root. -/
noncomputable def par (e : Fin T.m) : Fin T.b :=
  if T.graph.dist (T.ends e).1 r < T.graph.dist (T.ends e).2 r then (T.ends e).1 else (T.ends e).2

/-- The end of `e` that is farther from the root. -/
noncomputable def chi (e : Fin T.m) : Fin T.b :=
  if T.graph.dist (T.ends e).1 r < T.graph.dist (T.ends e).2 r then (T.ends e).2 else (T.ends e).1

theorem par_chi_spec (e : Fin T.m) :
    ((par T r e = (T.ends e).1 ∧ chi T r e = (T.ends e).2) ∨
      (par T r e = (T.ends e).2 ∧ chi T r e = (T.ends e).1)) ∧
    T.graph.dist (chi T r e) r = T.graph.dist (par T r e) r + 1 := by
  have h := (graph_isTree T).dist_eq_dist_add_one_of_adj r (graph_adj T e)
  rw [dist_comm (u := r) (v := (T.ends e).1), dist_comm (u := r) (v := (T.ends e).2)] at h
  unfold par chi
  by_cases hlt : T.graph.dist (T.ends e).1 r < T.graph.dist (T.ends e).2 r
  · rw [if_pos hlt, if_pos hlt]
    exact ⟨Or.inl ⟨rfl, rfl⟩, by omega⟩
  · rw [if_neg hlt, if_neg hlt]
    exact ⟨Or.inr ⟨rfl, rfl⟩, by omega⟩

theorem par_mem (e : Fin T.m) : par T r e = (T.ends e).1 ∨ par T r e = (T.ends e).2 := by
  rcases (par_chi_spec T r e).1 with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem chi_mem (e : Fin T.m) : chi T r e = (T.ends e).1 ∨ chi T r e = (T.ends e).2 := by
  rcases (par_chi_spec T r e).1 with ⟨-, h⟩ | ⟨-, h⟩
  · exact Or.inr h
  · exact Or.inl h

theorem dist_chi (e : Fin T.m) :
    T.graph.dist (chi T r e) r = T.graph.dist (par T r e) r + 1 := (par_chi_spec T r e).2

theorem par_ne_chi (e : Fin T.m) : par T r e ≠ chi T r e := by
  intro h
  have := dist_chi T r e
  rw [h] at this
  omega

theorem sym_par_chi (e : Fin T.m) :
    s((T.ends e).1, (T.ends e).2) = s(par T r e, chi T r e) := by
  rcases (par_chi_spec T r e).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    exact Sym2.eq_swap

theorem adj_par_chi (e : Fin T.m) : T.graph.Adj (par T r e) (chi T r e) := by
  have h := graph_adj T e
  rcases (par_chi_spec T r e).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact h
  · rw [h1, h2]
    exact h.symm

theorem edge_of_par_chi {e₁ e₂ : Fin T.m} (h1 : par T r e₁ = par T r e₂)
    (h2 : chi T r e₁ = chi T r e₂) : e₁ = e₂ := by
  apply T.ends_inj
  show s((T.ends e₁).1, (T.ends e₁).2) = s((T.ends e₂).1, (T.ends e₂).2)
  rw [sym_par_chi T r e₁, sym_par_chi T r e₂, h1, h2]

/-- The edge to the parent is determined by the child. -/
theorem chi_inj {e₁ e₂ : Fin T.m} (h : chi T r e₁ = chi T r e₂) : e₁ = e₂ := by
  refine edge_of_par_chi T r ?_ h
  have a1 := (adj_par_chi T r e₁).symm
  have a2 := (adj_par_chi T r e₂).symm
  rw [h] at a1
  refine parent_unique (graph_isTree T) (r := r) a1 a2 ?_ ?_
  · rw [← h]
    exact (dist_chi T r e₁).symm
  · exact (dist_chi T r e₂).symm

/-- The edge between a node and a neighbour closer to the root has that node as its child end. -/
theorem par_chi_of_edge {e : Fin T.m} {u v : Fin T.b}
    (h : ((T.ends e).1 = u ∧ (T.ends e).2 = v) ∨ ((T.ends e).1 = v ∧ (T.ends e).2 = u))
    (hd : T.graph.dist u r + 1 = T.graph.dist v r) : par T r e = u ∧ chi T r e = v := by
  obtain ⟨h1, h2⟩ := par_chi_spec T r e
  rcases h1 with ⟨a, c⟩ | ⟨a, c⟩ <;> rcases h with ⟨p, q⟩ | ⟨p, q⟩
  · exact ⟨a.trans p, c.trans q⟩
  · exfalso
    rw [c, a, q, p] at h2
    omega
  · exfalso
    rw [c, a, p, q] at h2
    omega
  · exact ⟨a.trans q, c.trans p⟩

/-- The earlier edges with the same parent. -/
noncomputable def sib (e : Fin T.m) : Finset (Fin T.m) :=
  open Classical in Finset.univ.filter (fun e' => e' < e ∧ par T r e' = par T r e)

theorem mem_sib {e e' : Fin T.m} : e' ∈ sib T r e ↔ e' < e ∧ par T r e' = par T r e := by
  simp [sib]

/-- The predecessor of the port of `e` in the chain at its parent: the port of the previous edge with
the same parent, or the parent itself. -/
noncomputable def pred (e : Fin T.m) : Fin T.b ⊕ Fin T.m :=
  open Classical in
  if h : (sib T r e).Nonempty then Sum.inr ((sib T r e).max' h) else Sum.inl (par T r e)

theorem pred_cases (e : Fin T.m) :
    (∃ e', pred T r e = Sum.inr e' ∧ e' < e ∧ par T r e' = par T r e ∧
      ∀ e'' ∈ sib T r e, e'' ≤ e') ∨
    (pred T r e = Sum.inl (par T r e) ∧ ¬ (sib T r e).Nonempty) := by
  classical
  by_cases h : (sib T r e).Nonempty
  · left
    refine ⟨(sib T r e).max' h, ?_, ((mem_sib T r).1 (Finset.max'_mem _ h)).1,
      ((mem_sib T r).1 (Finset.max'_mem _ h)).2, fun e'' he'' => Finset.le_max' _ _ he''⟩
    unfold pred
    rw [dif_pos h]
  · right
    refine ⟨?_, h⟩
    unfold pred
    rw [dif_neg h]

theorem pred_inr {e e' : Fin T.m} (h : pred T r e = Sum.inr e') :
    e' < e ∧ par T r e' = par T r e := by
  rcases pred_cases T r e with ⟨e'', h2, h3, h4, -⟩ | ⟨h2, -⟩
  · rw [h2] at h
    have : e'' = e' := Sum.inr.inj h
    subst this
    exact ⟨h3, h4⟩
  · rw [h2] at h
    cases h

theorem pred_inl {e : Fin T.m} {p : Fin T.b} (h : pred T r e = Sum.inl p) :
    p = par T r e ∧ ¬ (sib T r e).Nonempty := by
  rcases pred_cases T r e with ⟨e'', h2, -, -, -⟩ | ⟨h2, h3⟩
  · rw [h2] at h
    cases h
  · rw [h2] at h
    exact ⟨(Sum.inl.inj h).symm, h3⟩

theorem pred_inj {e₁ e₂ : Fin T.m} (h : pred T r e₁ = pred T r e₂) : e₁ = e₂ := by
  by_contra hne
  wlog hlt : e₁ < e₂ generalizing e₁ e₂
  · exact this h.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  rcases pred_cases T r e₂ with ⟨e', h2, -, hpar', hmax⟩ | ⟨h2, hemp⟩
  · rw [h2] at h
    obtain ⟨hlt1, hp1⟩ := pred_inr T r h
    have hmem : e₁ ∈ sib T r e₂ := (mem_sib T r).2 ⟨hlt, hp1.symm.trans hpar'⟩
    have := hmax e₁ hmem
    exact absurd hlt1 (not_lt.2 this)
  · rw [h2] at h
    have hp := (pred_inl T r h).1
    exact hemp ⟨e₁, (mem_sib T r).2 ⟨hlt, hp.symm⟩⟩

/-! ### The binary co-decomposition, indexed by nodes and ports -/

/-- The bags: the bag of a node, and at the port of `e` a copy of the bag of the parent end. -/
noncomputable def Dbag : Fin T.b ⊕ Fin T.m → Bag σ := Sum.elim T.bag (fun e => T.bag (par T r e))

theorem pred_bag (e : Fin T.m) : Dbag T r (pred T r e) = T.bag (par T r e) := by
  rcases pred_cases T r e with ⟨e', h, -, hp, -⟩ | ⟨h, -⟩
  · rw [h]
    exact congrArg T.bag hp
  · rw [h]
    rfl

/-- The edges: from the port of `e` to the child end of `e`, and from the port of `e` to its
predecessor in the chain. -/
noncomputable def Dends : Fin T.m ⊕ Fin T.m → (Fin T.b ⊕ Fin T.m) × (Fin T.b ⊕ Fin T.m) :=
  Sum.elim (fun e => (Sum.inr e, Sum.inl (chi T r e))) (fun e => (Sum.inr e, pred T r e))

/-- The adhesions: the adhesion of `e`, and on a chain edge the bag of the parent. -/
noncomputable def Dadh : Fin T.m ⊕ Fin T.m → Bag σ := Sum.elim T.adh (fun e => T.bag (par T r e))

noncomputable def Dgl :
    (e : Fin T.m ⊕ Fin T.m) → Fin (Dbag T r (Dends T r e).1).n → Fin (Dadh T r e).n
  | Sum.inl e => T.edgeMap e (par T r e) (par_mem T r e)
  | Sum.inr _ => id

noncomputable def Dgr :
    (e : Fin T.m ⊕ Fin T.m) → Fin (Dbag T r (Dends T r e).2).n → Fin (Dadh T r e).n
  | Sum.inl e => T.edgeMap e (chi T r e) (chi_mem T r e)
  | Sum.inr e => Fin.cast (congrArg Bag.n (pred_bag T r e))

theorem Dends_ne (e : Fin T.m ⊕ Fin T.m) : (Dends T r e).1 ≠ (Dends T r e).2 := by
  rcases e with e | e
  · exact Sum.inr_ne_inl
  · intro h
    have h' : Sum.inr e = pred T r e := h
    exact absurd (pred_inr T r h'.symm).1 (lt_irrefl e)

theorem Dends_inj :
    Function.Injective (fun e => s((Dends T r e).1, (Dends T r e).2)) := by
  rintro (e₁ | e₁) (e₂ | e₂) h
  · have h' : s((Sum.inr e₁ : Fin T.b ⊕ Fin T.m), Sum.inl (chi T r e₁)) =
        s(Sum.inr e₂, Sum.inl (chi T r e₂)) := h
    rcases Sym2.eq_iff.1 h' with ⟨a, -⟩ | ⟨a, -⟩
    · rw [Sum.inr.inj a]
    · cases a
  · exfalso
    have h' : s((Sum.inr e₁ : Fin T.b ⊕ Fin T.m), Sum.inl (chi T r e₁)) =
        s(Sum.inr e₂, pred T r e₂) := h
    rcases Sym2.eq_iff.1 h' with ⟨a, c⟩ | ⟨-, c⟩
    · have a' : e₁ = e₂ := Sum.inr.inj a
      subst a'
      exact par_ne_chi T r e₁ (pred_inl T r c.symm).1.symm
    · cases c
  · exfalso
    have h' : s((Sum.inr e₁ : Fin T.b ⊕ Fin T.m), pred T r e₁) =
        s(Sum.inr e₂, Sum.inl (chi T r e₂)) := h
    rcases Sym2.eq_iff.1 h' with ⟨a, c⟩ | ⟨a, -⟩
    · have a' : e₁ = e₂ := Sum.inr.inj a
      subst a'
      exact par_ne_chi T r e₁ (pred_inl T r c).1.symm
    · cases a
  · have h' : s((Sum.inr e₁ : Fin T.b ⊕ Fin T.m), pred T r e₁) =
        s(Sum.inr e₂, pred T r e₂) := h
    rcases Sym2.eq_iff.1 h' with ⟨a, -⟩ | ⟨a, c⟩
    · rw [Sum.inr.inj a]
    · exfalso
      have k1 := (pred_inr T r a.symm).1
      have k2 := (pred_inr T r c).1
      exact absurd k1 (not_lt.2 k2.le)

/-- The graph of the binary co-decomposition. -/
abbrev DG : SimpleGraph (Fin T.b ⊕ Fin T.m) :=
  SimpleGraph.fromEdgeSet (Set.range fun e => s((Dends T r e).1, (Dends T r e).2))

theorem DG_adj (e : Fin T.m ⊕ Fin T.m) : (DG T r).Adj (Dends T r e).1 (Dends T r e).2 :=
  (fromEdgeSet_adj _).2 ⟨⟨e, rfl⟩, Dends_ne T r e⟩

/-- A port is connected to the parent end of its edge, along the chain. -/
theorem reach_port (e : Fin T.m) :
    (DG T r).Reachable (Sum.inr e) (Sum.inl (par T r e)) := by
  induction e using WellFoundedLT.induction with
  | ind e ih =>
    have hadj : (DG T r).Adj (Sum.inr e) (pred T r e) := DG_adj T r (Sum.inr e)
    rcases pred_cases T r e with ⟨e', h, hlt, hp, -⟩ | ⟨h, -⟩
    · rw [h] at hadj
      have h2 := ih e' hlt
      rw [hp] at h2
      exact hadj.reachable.trans h2
    · rw [h] at hadj
      exact hadj.reachable

/-- Every node is connected to the root. -/
theorem reach_main : ∀ (n : ℕ) (t : Fin T.b), T.graph.dist t r = n →
    (DG T r).Reachable (Sum.inl t) (Sum.inl r) := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have : t = r := ((graph_isTree T).connected.dist_eq_zero_iff).1 ht
    rw [this]
  | succ n ih =>
    intro t ht
    have hne : t ≠ r := by
      rintro rfl
      rw [dist_self] at ht
      omega
    obtain ⟨t', hadj, hd⟩ := exists_adj_dist (graph_isTree T).connected hne
    obtain ⟨e, he⟩ := exists_edge_of_adj T hadj
    obtain ⟨hp, hc⟩ := par_chi_of_edge T r (u := t') (v := t) he.symm hd
    have h1 : (DG T r).Adj (Sum.inr e) (Sum.inl (chi T r e)) := DG_adj T r (Sum.inl e)
    rw [hc] at h1
    have h2 := reach_port T r e
    rw [hp] at h2
    exact h1.symm.reachable.trans (h2.trans (ih t' (by omega)))

theorem DG_isTree : (DG T r).IsTree := by
  rw [isTree_iff_connected_and_card]
  constructor
  · have hall : ∀ v, (DG T r).Reachable v (Sum.inl r) := by
      rintro (t | e)
      · exact reach_main T r _ t rfl
      · exact (reach_port T r e).trans (reach_main T r _ _ rfl)
    exact { preconnected := fun u v => (hall u).trans (hall v).symm, nonempty := ⟨Sum.inl r⟩ }
  · rw [card_edgeSet (Dends T r) (Dends_ne T r) (Dends_inj T r)]
    have h := edges_add_one T
    simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin]
    omega

/-- The binary co-decomposition, indexed by nodes and ports. -/
noncomputable def DD : GCD σ (Fin T.b ⊕ Fin T.m) (Fin T.m ⊕ Fin T.m) where
  bag := Dbag T r
  ends := Dends T r
  ends_ne := Dends_ne T r
  ends_inj := Dends_inj T r
  isTree := DG_isTree T r
  adh := Dadh T r
  gl := Dgl T r
  gr := Dgr T r
  gl_surj := by
    rintro (e | e)
    · exact edgeMap_surj T e (par T r e) (par_mem T r e)
    · exact Function.surjective_id
  gr_surj := by
    rintro (e | e)
    · exact edgeMap_surj T e (chi T r e) (chi_mem T r e)
    · exact (cast_bij (congrArg Bag.n (pred_bag T r e))).2
  gl_hom := by
    rintro (e | e)
    · exact edgeMap_hom T e (par T r e) (par_mem T r e)
    · exact fun i args hh => hh
  gr_hom := by
    rintro (e | e)
    · exact edgeMap_hom T e (chi T r e) (chi_mem T r e)
    · exact castHom (pred_bag T r e)

end B2

end CoDecompFO

namespace CoDecompFO

open FirstOrder

namespace B2

open TreeAux SimpleGraph

variable {σ : Sig} (T : CoDecomp σ) (r : Fin T.b)

/-! ### The limit of the binary co-decomposition -/

theorem edgeMap_fam_fst (x : (t : Fin T.b) → Fin (T.bag t).n) (e : Fin T.m) (s : Fin T.b)
    (hs : s = (T.ends e).1 ∨ s = (T.ends e).2) (h : s = (T.ends e).1) :
    T.edgeMap e s hs (x s) = T.gl e (x (T.ends e).1) := by
  subst h
  unfold CoDecomp.edgeMap
  rw [dif_pos rfl]

theorem edgeMap_fam_snd (x : (t : Fin T.b) → Fin (T.bag t).n) (e : Fin T.m) (s : Fin T.b)
    (hs : s = (T.ends e).1 ∨ s = (T.ends e).2) (h : s = (T.ends e).2) :
    T.edgeMap e s hs (x s) = T.gr e (x (T.ends e).2) := by
  subst h
  unfold CoDecomp.edgeMap
  rw [dif_neg (fun h => T.ends_ne e h.symm)]

/-- Matching on an edge, written with the parent and child ends. -/
theorem compat_iff (x : (t : Fin T.b) → Fin (T.bag t).n) (e : Fin T.m) :
    T.gl e (x (T.ends e).1) = T.gr e (x (T.ends e).2) ↔
      T.edgeMap e (par T r e) (par_mem T r e) (x (par T r e)) =
        T.edgeMap e (chi T r e) (chi_mem T r e) (x (chi T r e)) := by
  rcases (par_chi_spec T r e).1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [edgeMap_fam_fst T x e _ _ h1, edgeMap_fam_snd T x e _ _ h2]
  · rw [edgeMap_fam_snd T x e _ _ h1, edgeMap_fam_fst T x e _ _ h2]
    exact eq_comm

theorem cast_x (x : (t : Fin T.b) → Fin (T.bag t).n) (t' t : Fin T.b) (h : t' = t)
    (hn : (T.bag t').n = (T.bag t).n) : Fin.cast hn (x t') = x t := by
  subst h
  rfl

/-- The family on nodes and ports given by a family on nodes: a port carries the value at the parent
end of its edge. -/
noncomputable def thetaVal (x : (t : Fin T.b) → Fin (T.bag t).n) :
    (v : Fin T.b ⊕ Fin T.m) → Fin (Dbag T r v).n
  | Sum.inl t => x t
  | Sum.inr e => x (par T r e)

theorem theta_pred (x : (t : Fin T.b) → Fin (T.bag t).n) (e : Fin T.m) :
    ∀ (v : Fin T.b ⊕ Fin T.m) (_ : pred T r e = v) (hn : (Dbag T r v).n = (T.bag (par T r e)).n),
      Fin.cast hn (thetaVal T r x v) = x (par T r e) := by
  rintro (t | e') hv hn
  · exact cast_x T x _ _ (pred_inl T r hv).1 hn
  · exact cast_x T x _ _ (pred_inr T r hv).2 hn

/-- The matching family of the binary co-decomposition given by a matching family of `T`. -/
noncomputable def theta (x : T.Lim) : (DD T r).Lim :=
  ⟨thetaVal T r x.val, by
    rintro (e | e)
    · show T.edgeMap e (par T r e) (par_mem T r e) (x.val (par T r e)) =
        T.edgeMap e (chi T r e) (chi_mem T r e) (x.val (chi T r e))
      exact (compat_iff T r x.val e).1 (x.compat e)
    · show x.val (par T r e) =
        Fin.cast (congrArg Bag.n (pred_bag T r e)) (thetaVal T r x.val (pred T r e))
      exact (theta_pred T r x.val e _ rfl _).symm⟩

theorem theta_inj : Function.Injective (theta T r) := by
  intro x x' h
  apply CoDecomp.Lim.ext
  funext t
  exact congrFun (congrArg Subtype.val h) (Sum.inl t)

theorem cast_yl (y : (DD T r).Lim) (t' t : Fin T.b) (h : t' = t)
    (hn : (T.bag t').n = (T.bag t).n) :
    Fin.cast hn (y.1 (Sum.inl t')) = y.1 (Sum.inl t) := by
  subst h
  rfl

/-- In a matching family of the binary co-decomposition, a port carries the value at the parent end
of its edge. -/
theorem port_val (y : (DD T r).Lim) (e : Fin T.m) :
    (y.1 (Sum.inr e) : Fin (T.bag (par T r e)).n) = y.1 (Sum.inl (par T r e)) := by
  induction e using WellFoundedLT.induction with
  | ind e ih =>
    have key : ∀ (v : Fin T.b ⊕ Fin T.m) (_ : pred T r e = v)
        (hn : (Dbag T r v).n = (T.bag (par T r e)).n),
        Fin.cast hn (y.1 v) = y.1 (Sum.inl (par T r e)) := by
      rintro (t | e') hv hn
      · exact cast_yl T r y _ _ (pred_inl T r hv).1 hn
      · obtain ⟨hlt, hp⟩ := pred_inr T r hv
        exact (congrArg (Fin.cast hn) (ih e' hlt)).trans (cast_yl T r y _ _ hp hn)
    have h1 : (y.1 (Sum.inr e) : Fin (T.bag (par T r e)).n) =
        Fin.cast (congrArg Bag.n (pred_bag T r e)) (y.1 (pred T r e)) := y.2 (Sum.inr e)
    rw [h1]
    exact key _ rfl _

theorem theta_surj : Function.Surjective (theta T r) := by
  intro y
  have hc : ∀ e, T.gl e (y.1 (Sum.inl (T.ends e).1)) = T.gr e (y.1 (Sum.inl (T.ends e).2)) := by
    intro e
    refine (compat_iff T r (fun t => y.1 (Sum.inl t)) e).2 ?_
    have h1 : T.edgeMap e (par T r e) (par_mem T r e) (y.1 (Sum.inr e)) =
        T.edgeMap e (chi T r e) (chi_mem T r e) (y.1 (Sum.inl (chi T r e))) := y.2 (Sum.inl e)
    rw [port_val T r y e] at h1
    exact h1
  refine ⟨⟨fun t => y.1 (Sum.inl t), hc⟩, ?_⟩
  apply Subtype.ext
  funext v
  rcases v with t | e
  · rfl
  · exact (port_val T r y e).symm

theorem theta_holds (i : Fin σ.r) (args : Fin (σ.ar i) → T.Lim) :
    σ.holds i (theta T r ∘ args) ↔ σ.holds i args := by
  show (∀ v, σ.holds i (fun j => thetaVal T r (args j).val v)) ↔
    (∀ t, σ.holds i (fun j => (args j).val t))
  constructor
  · intro h t
    exact h (Sum.inl t)
  · intro h v
    rcases v with t | e
    · exact h t
    · exact h (par T r e)

theorem theta_val (x : T.Lim) (t : Fin T.b) :
    ∀ (v : Fin T.b ⊕ Fin T.m), v = Sum.inl t → ((theta T r x).1 v).val = (x.val t).val := by
  rintro _ rfl
  rfl

/-! ### The edges at a node of the binary co-decomposition -/

theorem inc_main (t : Fin T.b) : ((DD T r).inc (Sum.inl t)).ncard ≤ 2 := by
  have hsub : (DD T r).inc (Sum.inl t) ⊆
      (Sum.inl '' {e | chi T r e = t}) ∪ (Sum.inr '' {e | pred T r e = Sum.inl t}) := by
    rintro (e | e) h
    · left
      refine ⟨e, ?_, rfl⟩
      rcases h with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact Sum.inl.inj h
    · right
      refine ⟨e, ?_, rfl⟩
      rcases h with h | h
      · exact absurd h Sum.inr_ne_inl
      · exact h
  have h1 : (Sum.inl '' {e | chi T r e = t} : Set (Fin T.m ⊕ Fin T.m)).ncard ≤ 1 := by
    rw [Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_le_one (Set.toFinite _)]
    intro a ha c hc
    exact chi_inj T r (ha.trans hc.symm)
  have h2 : (Sum.inr '' {e | pred T r e = Sum.inl t} : Set (Fin T.m ⊕ Fin T.m)).ncard ≤ 1 := by
    rw [Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_le_one (Set.toFinite _)]
    intro a ha c hc
    exact pred_inj T r (ha.trans hc.symm)
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 := Set.ncard_union_le (Sum.inl '' {e | chi T r e = t} : Set (Fin T.m ⊕ Fin T.m))
    (Sum.inr '' {e | pred T r e = Sum.inl t})
  omega

theorem inc_port (e₀ : Fin T.m) : ((DD T r).inc (Sum.inr e₀)).ncard ≤ 3 := by
  have hsub : (DD T r).inc (Sum.inr e₀) ⊆
      ({Sum.inl e₀} : Set (Fin T.m ⊕ Fin T.m)) ∪
        (({Sum.inr e₀} : Set (Fin T.m ⊕ Fin T.m)) ∪
          (Sum.inr '' {e | pred T r e = Sum.inr e₀})) := by
    rintro (e | e) h
    · left
      rcases h with h | h
      · exact Set.mem_singleton_iff.2 (congrArg Sum.inl (Sum.inr.inj h))
      · exact absurd h Sum.inl_ne_inr
    · right
      rcases h with h | h
      · left
        exact Set.mem_singleton_iff.2 (congrArg Sum.inr (Sum.inr.inj h))
      · right
        exact ⟨e, h, rfl⟩
  have h2 : (Sum.inr '' {e | pred T r e = Sum.inr e₀} : Set (Fin T.m ⊕ Fin T.m)).ncard ≤ 1 := by
    rw [Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_le_one (Set.toFinite _)]
    intro a ha c hc
    exact pred_inj T r (ha.trans hc.symm)
  have h3 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 := Set.ncard_union_le ({Sum.inl e₀} : Set (Fin T.m ⊕ Fin T.m))
    (({Sum.inr e₀} : Set (Fin T.m ⊕ Fin T.m)) ∪ (Sum.inr '' {e | pred T r e = Sum.inr e₀}))
  have h5 := Set.ncard_union_le ({Sum.inr e₀} : Set (Fin T.m ⊕ Fin T.m))
    (Sum.inr '' {e | pred T r e = Sum.inr e₀})
  have h6 : ({Sum.inl e₀} : Set (Fin T.m ⊕ Fin T.m)).ncard = 1 := Set.ncard_singleton _
  have h7 : ({Sum.inr e₀} : Set (Fin T.m ⊕ Fin T.m)).ncard = 1 := Set.ncard_singleton _
  omega

/-! ### Width -/

theorem width_eq {b m : ℕ} (eV : Fin T.b ⊕ Fin T.m ≃ Fin b) (eE : Fin T.m ⊕ Fin T.m ≃ Fin m) :
    width ((DD T r).toCoDecomp eV eE) = width T := by
  apply le_antisymm
  · refine Finset.sup_le fun i _ => ?_
    show (Dbag T r (eV.symm i)).n ≤ width T
    rcases eV.symm i with t | e
    · exact Finset.le_sup (f := fun t => (T.bag t).n) (Finset.mem_univ t)
    · exact Finset.le_sup (f := fun t => (T.bag t).n) (Finset.mem_univ (par T r e))
  · refine Finset.sup_le fun t _ => ?_
    have h : (T.bag t).n = (((DD T r).toCoDecomp eV eE).bag (eV (Sum.inl t))).n :=
      (congrArg Bag.n (bag_symm (DD T r) eV (Sum.inl t))).symm
    rw [h]
    exact Finset.le_sup (f := fun i => (((DD T r).toCoDecomp eV eE).bag i).n) (Finset.mem_univ _)

end B2

open B2 TreeAux in
theorem b2_main {σ : Sig} (T : CoDecomp σ) :
    ∃ (Ts : CoDecomp σ) (rs : Fin Ts.b),
      (∀ t, {e | Ts.IsChildEdge rs t e}.ncard ≤ 2) ∧
      width Ts = width T ∧
      Ts.b ≤ 4 * T.b ∧
      ∃ (u : T.Lim ≃[σ.lang] Ts.Lim) (ι : Fin T.b → Fin Ts.b),
        ∀ t, Ts.bag (ι t) = T.bag t ∧ ∀ x, ((u x).val (ι t)).val = (x.val t).val := by
  obtain ⟨r⟩ : Nonempty (Fin T.b) := (graph_isTree T).connected.nonempty
  let eV : Fin T.b ⊕ Fin T.m ≃ Fin (T.b + T.m) := finSumFinEquiv
  let eE : Fin T.m ⊕ Fin T.m ≃ Fin (T.m + T.m) := finSumFinEquiv
  refine ⟨(DD T r).toCoDecomp eV eE, eV (Sum.inl r), ?_, width_eq T r eV eE, ?_, ?_⟩
  · intro i
    apply child_ncard_le (DD T r) eV eE
    rcases h : eV.symm i with t | e
    · left
      exact inc_main T r t
    · right
      refine ⟨?_, inc_port T r e⟩
      intro hi
      rw [hi, Equiv.symm_apply_apply] at h
      cases h
  · show T.b + T.m ≤ 4 * T.b
    have := edges_add_one T
    omega
  · have hb : Function.Bijective ((DD T r).toLim eV eE ∘ theta T r) :=
      Function.Bijective.comp ⟨toLim_inj (DD T r) eV eE, toLim_surj (DD T r) eV eE⟩
        ⟨theta_inj T r, theta_surj T r⟩
    refine ⟨mkEquiv ((DD T r).toLim eV eE ∘ theta T r) hb
      (fun i args => (toLim_holds (DD T r) eV eE i (theta T r ∘ args)).trans
        (theta_holds T r i args)), fun t => eV (Sum.inl t), fun t =>
      ⟨bag_symm (DD T r) eV (Sum.inl t), fun x => ?_⟩⟩
    show ((theta T r x).1 (eV.symm (eV (Sum.inl t)))).val = (x.val t).val
    exact theta_val T r x t _ (eV.symm_apply_apply _)

end CoDecompFO

open CoDecompFO FirstOrder

theorem solution {σ : Sig} (T : CoDecomp σ) :
    ∃ (Ts : CoDecomp σ) (rs : Fin Ts.b),
      (∀ t, {e | Ts.IsChildEdge rs t e}.ncard ≤ 2) ∧
      width Ts = width T ∧
      Ts.b ≤ 4 * T.b ∧
      ∃ (u : T.Lim ≃[σ.lang] Ts.Lim) (ι : Fin T.b → Fin Ts.b),
        ∀ t, Ts.bag (ι t) = T.bag t ∧ ∀ x, ((u x).val (ι t)).val = (x.val t).val :=
  CoDecompFO.b2_main T
