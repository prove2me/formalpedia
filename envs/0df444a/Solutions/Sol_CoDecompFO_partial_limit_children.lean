-- Prove2me | solution 1 for CoDecompFO.partial_limit_children
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:28:34.965182+00:00
-- url     : https://prove2.me/submissions/acd60fc2-55c2-47fc-a892-680b3f5fe8a6

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

namespace PLC

open TreeAux

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

theorem mkEquiv_apply {M N : Type} [σ.lang.Structure M] [σ.lang.Structure N] (f : M → N)
    (hb : Function.Bijective f)
    (hf : ∀ (i : Fin σ.r) (args : Fin (σ.ar i) → M), σ.holds i (f ∘ args) ↔ σ.holds i args)
    (x : M) : mkEquiv f hb hf x = f x := rfl

variable (T : CoDecomp σ)

theorem mem_subtree_root (r s : Fin T.b) : s ∈ T.subtree r r := by
  simp [CoDecomp.subtree]

/-! ### The partial limit at the root -/

/-- A matching family on the subtree at the root, as a matching family. -/
def ofRoot (r : Fin T.b) (x : T.PartialLim r r) : T.Lim :=
  ⟨fun s => x.val ⟨s, mem_subtree_root T r s⟩,
    fun e => x.compat e (mem_subtree_root T r _) (mem_subtree_root T r _)⟩

theorem ofRoot_bij (r : Fin T.b) : Function.Bijective (ofRoot T r) := by
  constructor
  · intro x x' h
    apply CoDecomp.LimOn.ext
    funext s
    exact congrFun (congrArg CoDecomp.Lim.val h) s.1
  · intro y
    exact ⟨⟨fun s => y.val s.1, fun e _ _ => y.compat e⟩, rfl⟩

theorem ofRoot_holds (r : Fin T.b) (i : Fin σ.r) (args : Fin (σ.ar i) → T.PartialLim r r) :
    σ.holds i (ofRoot T r ∘ args) ↔ σ.holds i args := by
  show (∀ t, σ.holds i (fun j => (args j).val ⟨t, _⟩)) ↔
    (∀ s : T.subtree r r, σ.holds i (fun j => (args j).val s))
  constructor
  · intro h s
    exact h s.1
  · intro h t
    exact h ⟨t, mem_subtree_root T r t⟩

/-! ### The partial limit at a node as an iterated pullback -/

/-- The tuple of the coordinate at `t` and the restrictions to the subtrees of the children. -/
def toTuples (r t : Fin T.b) (x : T.PartialLim r t) : T.ChildTuples r t :=
  ⟨T.partialProj r t x, fun e => restrict T (subtree_child_subset T e.2) x,
    fun e => edgeMap_compat T x e.1 t (T.child e.1 t) e.2.top_mem e.2.child_mem
      (T.mem_subtree_self r t) (subtree_child_subset T e.2 (T.mem_subtree_self r _))
      (adj_child T e.2).ne⟩

theorem toTuples_holds (r t : Fin T.b) (i : Fin σ.r) (args : Fin (σ.ar i) → T.PartialLim r t) :
    σ.holds i (toTuples T r t ∘ args) ↔ σ.holds i args := by
  show (σ.holds i (fun j => (args j).val ⟨t, _⟩) ∧
      ∀ e : {e // T.IsChildEdge r t e}, ∀ s : T.subtree r (T.child e.1 t),
        σ.holds i (fun j => (args j).val ⟨s.1, _⟩)) ↔
    (∀ s : T.subtree r t, σ.holds i (fun j => (args j).val s))
  constructor
  · rintro ⟨h1, h2⟩ ⟨s, hs⟩
    by_cases hst : s = t
    · subst hst
      exact h1
    · obtain ⟨e, he, hse⟩ := exists_child_of_mem T hs hst
      exact h2 ⟨e, he⟩ ⟨s, hse⟩
  · intro h
    exact ⟨h ⟨t, _⟩, fun e s => h ⟨s.1, _⟩⟩

theorem toTuples_inj (r t : Fin T.b) : Function.Injective (toTuples T r t) := by
  intro x x' h
  apply CoDecomp.LimOn.ext
  funext s
  obtain ⟨s, hs⟩ := s
  by_cases hst : s = t
  · subst hst
    exact congrArg CoDecomp.ChildTuples.top h
  · obtain ⟨e, he, hse⟩ := exists_child_of_mem T hs hst
    have h2 := congrFun (congrArg CoDecomp.ChildTuples.below h) ⟨e, he⟩
    exact congrFun (congrArg CoDecomp.LimOn.val h2) ⟨s, hse⟩

/-- The value at `s` of the family glued from a tuple. -/
noncomputable def glueVal {r t : Fin T.b} (y : T.ChildTuples r t) (s : Fin T.b)
    (hs : s ∈ T.subtree r t) : Fin (T.bag s).n :=
  open Classical in
  if h : s = t then h ▸ y.top
  else (y.below ⟨Classical.choose (exists_child_of_mem T hs h),
      (Classical.choose_spec (exists_child_of_mem T hs h)).1⟩).val
    ⟨s, (Classical.choose_spec (exists_child_of_mem T hs h)).2⟩

theorem glueVal_top {r t : Fin T.b} (y : T.ChildTuples r t) (ht : t ∈ T.subtree r t) :
    glueVal T y t ht = y.top := by
  unfold glueVal
  rw [dif_pos rfl]

theorem glueVal_below {r t : Fin T.b} (y : T.ChildTuples r t) (s : Fin T.b)
    (hs : s ∈ T.subtree r t) (e : Fin T.m) (he : T.IsChildEdge r t e)
    (hse : s ∈ T.subtree r (T.child e t)) :
    glueVal T y s hs = (y.below ⟨e, he⟩).val ⟨s, hse⟩ := by
  have hst : s ≠ t := by
    rintro rfl
    exact not_mem_subtree_child T he hse
  have key : ∀ (E : Fin T.m) (hE : T.IsChildEdge r t E) (hsE : s ∈ T.subtree r (T.child E t)),
      (y.below ⟨E, hE⟩).val ⟨s, hsE⟩ = (y.below ⟨e, he⟩).val ⟨s, hse⟩ := by
    intro E hE hsE
    have hEe : E = e := child_edge_unique T hE he hsE hse
    subst hEe
    rfl
  unfold glueVal
  rw [dif_neg hst]
  exact key _ _ _

/-- The adhesion map at `t`, applied to the top coordinate, in terms of the glued family. -/
theorem edgeMap_top_fst {r t : Fin T.b} (y : T.ChildTuples r t) (e : Fin T.m)
    (hs : t = (T.ends e).1 ∨ t = (T.ends e).2) (h : t = (T.ends e).1)
    (m' : (T.ends e).1 ∈ T.subtree r t) :
    T.edgeMap e t hs y.top = T.gl e (glueVal T y (T.ends e).1 m') := by
  subst h
  rw [glueVal_top]
  unfold CoDecomp.edgeMap
  rw [dif_pos rfl]

theorem edgeMap_top_snd {r t : Fin T.b} (y : T.ChildTuples r t) (e : Fin T.m)
    (hs : t = (T.ends e).1 ∨ t = (T.ends e).2) (h : t = (T.ends e).2)
    (m' : (T.ends e).2 ∈ T.subtree r t) :
    T.edgeMap e t hs y.top = T.gr e (glueVal T y (T.ends e).2 m') := by
  subst h
  rw [glueVal_top]
  unfold CoDecomp.edgeMap
  rw [dif_neg (fun h => T.ends_ne e h.symm)]

theorem glue_compat {r t : Fin T.b} (y : T.ChildTuples r t) (e' : Fin T.m)
    (h₁ : (T.ends e').1 ∈ T.subtree r t) (h₂ : (T.ends e').2 ∈ T.subtree r t) :
    T.gl e' (glueVal T y _ h₁) = T.gr e' (glueVal T y _ h₂) := by
  have hc := (graph_isTree T).connected
  by_cases a1 : (T.ends e').1 = t
  · -- `e'` is a child edge of `t`, with child `(ends e').2`
    have hd : T.graph.dist (T.ends e').2 r = T.graph.dist t r + 1 := by
      have k1 : T.graph.dist (T.ends e').2 r =
          T.graph.dist (T.ends e').2 t + T.graph.dist t r := h₂
      have k2 : T.graph.dist (T.ends e').2 t = 1 := by
        rw [← a1]
        exact SimpleGraph.dist_eq_one_iff_adj.2 (graph_adj T e').symm
      omega
    have he' : T.IsChildEdge r t e' := Or.inl ⟨a1, hd⟩
    have hch : T.child e' t = (T.ends e').2 := by
      rcases (child_spec T he').1 with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · exact b2.symm
      · exact absurd (a1.trans b1.symm) (T.ends_ne e')
    have m₂ : (T.ends e').2 ∈ T.subtree r (T.child e' t) := by
      rw [hch]
      exact T.mem_subtree_self r _
    have hy := y.compat ⟨e', he'⟩
    have hy' : T.edgeMap e' t he'.top_mem y.top =
        T.edgeMap e' (T.child e' t) he'.child_mem
          ((y.below ⟨e', he'⟩).val ⟨T.child e' t, T.mem_subtree_self r _⟩) := hy
    rw [edgeMap_top_fst T y e' he'.top_mem a1.symm h₁,
      edgeMap_val_snd T (y.below ⟨e', he'⟩) e' _ he'.child_mem _ hch m₂] at hy'
    rw [hy', glueVal_below T y _ h₂ e' he' m₂]
  · by_cases a2 : (T.ends e').2 = t
    · have hd : T.graph.dist (T.ends e').1 r = T.graph.dist t r + 1 := by
        have k1 : T.graph.dist (T.ends e').1 r =
            T.graph.dist (T.ends e').1 t + T.graph.dist t r := h₁
        have k2 : T.graph.dist (T.ends e').1 t = 1 := by
          rw [← a2]
          exact SimpleGraph.dist_eq_one_iff_adj.2 (graph_adj T e')
        omega
      have he' : T.IsChildEdge r t e' := Or.inr ⟨a2, hd⟩
      have hch : T.child e' t = (T.ends e').1 := by
        rcases (child_spec T he').1 with ⟨b1, b2⟩ | ⟨b1, b2⟩
        · exact absurd b1 a1
        · exact b2.symm
      have m₁ : (T.ends e').1 ∈ T.subtree r (T.child e' t) := by
        rw [hch]
        exact T.mem_subtree_self r _
      have hy := y.compat ⟨e', he'⟩
      have hy' : T.edgeMap e' t he'.top_mem y.top =
          T.edgeMap e' (T.child e' t) he'.child_mem
            ((y.below ⟨e', he'⟩).val ⟨T.child e' t, T.mem_subtree_self r _⟩) := hy
      rw [edgeMap_top_snd T y e' he'.top_mem a2.symm h₂,
        edgeMap_val_fst T (y.below ⟨e', he'⟩) e' _ he'.child_mem _ hch m₁] at hy'
      rw [hy', glueVal_below T y _ h₁ e' he' m₁]
    · -- both endpoints lie in the subtree of the same child
      obtain ⟨e, he, m₁⟩ := exists_child_of_mem T h₁ a1
      have m₂ : (T.ends e').2 ∈ T.subtree r (T.child e t) := by
        by_contra hnot
        exact a2 (cross_child T he (graph_adj T e') m₁ hnot).2
      rw [glueVal_below T y _ h₁ e he m₁, glueVal_below T y _ h₂ e he m₂]
      exact (y.below ⟨e, he⟩).compat e' m₁ m₂

theorem toTuples_surj (r t : Fin T.b) : Function.Surjective (toTuples T r t) := by
  intro y
  refine ⟨⟨fun s => glueVal T y s.1 s.2, fun e' h₁ h₂ => glue_compat T y e' h₁ h₂⟩, ?_⟩
  apply CoDecomp.ChildTuples.ext
  · exact glueVal_top T y (T.mem_subtree_self r t)
  · funext e
    apply CoDecomp.LimOn.ext
    funext s
    exact glueVal_below T y s.1 (subtree_child_subset T e.2 s.2) e.1 e.2 s.2

theorem toTuples_bij (r t : Fin T.b) : Function.Bijective (toTuples T r t) :=
  ⟨toTuples_inj T r t, toTuples_surj T r t⟩

end PLC

open PLC TreeAux in
theorem plc_main {σ : Sig} (T : CoDecomp σ) (r : Fin T.b) :
    (∀ t : Fin T.b, ∃ u : T.PartialLim r t ≃[σ.lang] T.ChildTuples r t,
      ∀ x : T.PartialLim r t,
        (u x).top = T.partialProj r t x ∧
        ∀ (e : {e // T.IsChildEdge r t e}) (s : Fin T.b)
          (hc : s ∈ T.subtree r (T.child e.1 t)) (ht : s ∈ T.subtree r t),
          ((u x).below e).val ⟨s, hc⟩ = x.val ⟨s, ht⟩) ∧
    (∃ v : T.PartialLim r r ≃[σ.lang] T.Lim,
      ∀ (x : T.PartialLim r r) (s : Fin T.b) (hs : s ∈ T.subtree r r),
        (v x).val s = x.val ⟨s, hs⟩) := by
  refine ⟨fun t => ⟨mkEquiv (toTuples T r t) (toTuples_bij T r t)
    (toTuples_holds T r t), ?_⟩, ⟨mkEquiv (ofRoot T r) (ofRoot_bij T r) (ofRoot_holds T r), ?_⟩⟩
  · intro x
    exact ⟨rfl, fun e s hc ht => rfl⟩
  · intro x s hs
    rfl

end CoDecompFO

open CoDecompFO FirstOrder

theorem solution {σ : Sig} (T : CoDecomp σ) (r : Fin T.b) :
    (∀ t : Fin T.b, ∃ u : T.PartialLim r t ≃[σ.lang] T.ChildTuples r t,
      ∀ x : T.PartialLim r t,
        (u x).top = T.partialProj r t x ∧
        ∀ (e : {e // T.IsChildEdge r t e}) (s : Fin T.b)
          (hc : s ∈ T.subtree r (T.child e.1 t)) (ht : s ∈ T.subtree r t),
          ((u x).below e).val ⟨s, hc⟩ = x.val ⟨s, ht⟩) ∧
    (∃ v : T.PartialLim r r ≃[σ.lang] T.Lim,
      ∀ (x : T.PartialLim r r) (s : Fin T.b) (hs : s ∈ T.subtree r r),
        (v x).val s = x.val ⟨s, hs⟩) :=
  CoDecompFO.plc_main T r
