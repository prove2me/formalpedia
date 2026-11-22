-- Prove2me | solution 1 for CoDecompFO.observation_5_79
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-21T22:23:59.821177+00:00
-- url     : https://prove2.me/submissions/1a5d4b16-9226-42d8-a8b5-ab54cc3571fb

import Mathlib
import Definitions.Def_CoDecompFO_HTh
import Definitions.Def_CoDecompFO_Lim

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

namespace Obs

open TreeAux

variable {σ : Sig}

/-- Heads are invariant under a map that preserves and reflects the relations. -/
theorem atomsOf_map {G G' : Type} [σ.lang.Structure G] [σ.lang.Structure G'] (f : G → G')
    (hf : ∀ (i : Fin σ.r) (args : Fin (σ.ar i) → G), σ.holds i (f ∘ args) ↔ σ.holds i args)
    (k : ℕ) (l : List G) : atomsOf σ k (l.map f) = atomsOf σ k l := by
  ext A
  constructor
  · rintro ⟨args, h1, h2⟩
    have h3 : ∀ j, ∃ a, l[(A.2 j).val]? = some a ∧ f a = args j := by
      intro j
      have h4 := h1 j
      rw [List.getElem?_map] at h4
      exact Option.map_eq_some_iff.1 h4
    choose a ha1 ha2 using h3
    refine ⟨a, ha1, ?_⟩
    have h5 : args = f ∘ a := by
      funext j
      exact (ha2 j).symm
    rw [h5] at h2
    exact (hf _ _).1 h2
  · rintro ⟨args, h1, h2⟩
    refine ⟨f ∘ args, ?_, (hf _ _).2 h2⟩
    intro j
    rw [List.getElem?_map, h1 j]
    rfl

/-- The head induced on a pullback is the intersection of the heads induced on the two factors. -/
theorem atomsOf_fib {A B K : Type} [σ.lang.Structure A] [σ.lang.Structure B] (g : A → K)
    (h : B → K) (k : ℕ) (l : List (Fib g h)) :
    atomsOf σ k l = atomsOf σ k (l.map Fib.fst) ∩ atomsOf σ k (l.map Fib.snd) := by
  ext N
  constructor
  · rintro ⟨args, h1, h2⟩
    have h2' : σ.holds N.1 (fun j => (args j).fst) ∧ σ.holds N.1 (fun j => (args j).snd) := h2
    refine ⟨⟨fun j => (args j).fst, fun j => ?_, h2'.1⟩, ⟨fun j => (args j).snd, fun j => ?_, h2'.2⟩⟩
    · rw [List.getElem?_map, h1 j]
      rfl
    · rw [List.getElem?_map, h1 j]
      rfl
  · rintro ⟨⟨a1, h1, h2⟩, ⟨a2, h3, h4⟩⟩
    have h5 : ∀ j, ∃ z, l[(N.2 j).val]? = some z ∧ z.fst = a1 j ∧ z.snd = a2 j := by
      intro j
      have e1 := h1 j
      have e3 := h3 j
      rw [List.getElem?_map] at e1 e3
      obtain ⟨z, hz, hz1⟩ := Option.map_eq_some_iff.1 e1
      rw [hz] at e3
      exact ⟨z, hz, hz1, Option.some.inj e3⟩
    choose z hz1 hz2 hz3 using h5
    refine ⟨z, hz1, ?_⟩
    show σ.holds N.1 (fun j => (z j).fst) ∧ σ.holds N.1 (fun j => (z j).snd)
    have e1 : (fun j => (z j).fst) = a1 := funext hz2
    have e2 : (fun j => (z j).snd) = a2 := funext hz3
    rw [e1, e2]
    exact ⟨h2, h4⟩

/-- The induced hypothetical of the full strategy has one personality at each point: all responses. -/
theorem ind_full_succ {G : Type} [σ.lang.Structure G] (k m : ℕ) (l : List G) (x : G) :
    ind σ k (m + 1) (Strat.full G (m + 1)) l x =
      {Set.range (fun y : G => (y, ind σ k m (Strat.full G m) (l ++ [x, y])))} := by
  show ({(fun c : G × Strat G m => (c.1, ind σ k m c.2 (l ++ [x, c.1]))) ''
      Set.range (fun y : G => (y, Strat.full G m))} : Set (Set (G × HTh σ G k m))) = _
  rw [← Set.range_comp]
  rfl

/-- The personalities of the projection of the full strategy's induced hypothetical. -/
theorem push_ind_full_succ {G P : Type} [σ.lang.Structure G] (f : G → P) (k m : ℕ) (l : List G)
    (x' : P) :
    push f (m + 1) (ind σ k (m + 1) (Strat.full G (m + 1)) l) x' =
      {q | ∃ x, f x = x' ∧ q = Set.range (fun y : G =>
        (f y, push f m (ind σ k m (Strat.full G m) (l ++ [x, y]))))} := by
  apply Set.ext
  intro q
  constructor
  · rintro ⟨x, p, hx, hp, rfl⟩
    rw [ind_full_succ, Set.mem_singleton_iff] at hp
    subst hp
    refine ⟨x, hx, ?_⟩
    rw [← Set.range_comp]
    rfl
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, Set.range (fun y : G => (y, ind σ k m (Strat.full G m) (l ++ [x, y]))), hx, ?_, ?_⟩
    · rw [ind_full_succ]
      exact Set.mem_singleton _
    · rw [← Set.range_comp]
      rfl

/-- Projection along a surjection that preserves and reflects the relations takes the full strategy's
induced hypothetical to the full strategy's induced hypothetical. -/
theorem push_ind_full {G G' : Type} [σ.lang.Structure G] [σ.lang.Structure G'] (f : G → G')
    (hf : ∀ (i : Fin σ.r) (args : Fin (σ.ar i) → G), σ.holds i (f ∘ args) ↔ σ.holds i args)
    (hs : Function.Surjective f) (k : ℕ) :
    ∀ (m : ℕ) (l : List G),
      push f m (ind σ k m (Strat.full G m) l) = ind σ k m (Strat.full G' m) (l.map f) := by
  intro m
  induction m with
  | zero =>
    intro l
    show ({atomsOf σ k l} : Set (Set (σ.Atom k))) = {atomsOf σ k (l.map f)}
    rw [atomsOf_map f hf]
  | succ m ih =>
    intro l
    funext x'
    rw [push_ind_full_succ, ind_full_succ]
    have key : ∀ x : G,
        Set.range (fun y : G => (f y, push f m (ind σ k m (Strat.full G m) (l ++ [x, y])))) =
          Set.range (fun y' : G' => (y', ind σ k m (Strat.full G' m) (l.map f ++ [f x, y']))) := by
      intro x
      have e : (fun y : G => (f y, push f m (ind σ k m (Strat.full G m) (l ++ [x, y])))) =
          (fun y' : G' => (y', ind σ k m (Strat.full G' m) (l.map f ++ [f x, y']))) ∘ f := by
        funext y
        show (f y, _) = (f y, _)
        rw [ih]
        simp
      rw [e]
      exact hs.range_comp _
    apply Set.ext
    intro q
    constructor
    · rintro ⟨x, rfl, rfl⟩
      rw [key x]
      exact Set.mem_singleton _
    · intro hq
      rw [Set.mem_singleton_iff] at hq
      subst hq
      obtain ⟨x, rfl⟩ := hs x'
      exact ⟨x, rfl, (key x).symm⟩

/-- Projections compose. -/
theorem push_push {k : ℕ} {P Q R : Type} (f : P → Q) (g : Q → R) :
    ∀ (m : ℕ) (A : HTh σ P k m), push g m (push f m A) = push (g ∘ f) m A := by
  intro m
  induction m with
  | zero =>
    intro A
    rfl
  | succ m ih =>
    intro A
    funext x''
    apply Set.ext
    intro q
    have e : (fun c : P × HTh σ P k m => (g (f c.1), push g m (push f m c.2))) =
        (fun c : P × HTh σ P k m => ((g ∘ f) c.1, push (g ∘ f) m c.2)) := by
      funext c
      rw [ih]
      rfl
    constructor
    · rintro ⟨x', p', hx', ⟨x, p, hx, hp, rfl⟩, rfl⟩
      refine ⟨x, p, ?_, hp, ?_⟩
      · rw [Function.comp_apply, hx, hx']
      · rw [Set.image_image]
        exact congrArg (fun F => F '' p) e
    · rintro ⟨x, p, hx, hp, rfl⟩
      refine ⟨f x, (fun c : P × HTh σ P k m => (f c.1, push f m c.2)) '' p, hx,
        ⟨x, p, rfl, hp, rfl⟩, ?_⟩
      rw [Set.image_image]
      exact (congrArg (fun F => F '' p) e).symm

section Pullback

variable {Ah Bh P Q K : Type} [σ.lang.Structure Ah] [σ.lang.Structure Bh]

/-- The map `X̂ = Â ×_K B̂ → P ×_K Q` induced by `a` and `b`. -/
def fibMap (a : Ah → P) (b : Bh → Q) (g : P → K) (h : Q → K) (z : Fib (g ∘ a) (h ∘ b)) : Fib g h :=
  ⟨a z.fst, b z.snd, z.eq⟩

/-- Clause (1): the pullback of the projections of the full strategies is the projection of the full
strategy on the pullback. -/
theorem pb_full (a : Ah → P) (b : Bh → Q) (g : P → K) (h : Q → K) (k : ℕ) :
    ∀ (m : ℕ) (l : List (Fib (g ∘ a) (h ∘ b))),
      push (σ := σ) (k := k) (fibMap a b g h) m (ind σ k m (Strat.full _ m) l) =
        pb g h m
          (push a m (ind σ k m (Strat.full _ m) (l.map Fib.fst)))
          (push b m (ind σ k m (Strat.full _ m) (l.map Fib.snd))) := by
  intro m
  induction m with
  | zero =>
    intro l
    show ({atomsOf σ k l} : Set (Set (σ.Atom k))) =
      {N | ∃ N₁ ∈ ({atomsOf σ k (l.map Fib.fst)} : Set (Set (σ.Atom k))),
        ∃ N₂ ∈ ({atomsOf σ k (l.map Fib.snd)} : Set (Set (σ.Atom k))), N = N₁ ∩ N₂}
    apply Set.ext
    intro N
    constructor
    · intro hN
      rw [Set.mem_singleton_iff] at hN
      subst hN
      exact ⟨_, Set.mem_singleton _, _, Set.mem_singleton _, atomsOf_fib _ _ k l⟩
    · rintro ⟨N₁, hN₁, N₂, hN₂, rfl⟩
      rw [Set.mem_singleton_iff] at hN₁ hN₂
      subst hN₁
      subst hN₂
      exact (atomsOf_fib _ _ k l).symm
  | succ m ih =>
    intro l
    -- the responses at `x`, on both sides
    have key : ∀ x : Fib (g ∘ a) (h ∘ b),
        Set.range (fun y : Fib (g ∘ a) (h ∘ b) =>
          (fibMap a b g h y, push (σ := σ) (k := k) (fibMap a b g h) m
            (ind σ k m (Strat.full _ m) (l ++ [x, y])))) =
        {c : Fib g h × HTh σ (Fib g h) k m | ∃ c₁ c₂,
          (c.1.fst, c₁) ∈ Set.range (fun y₁ : Ah =>
            (a y₁, push a m (ind σ k m (Strat.full _ m) (l.map Fib.fst ++ [x.fst, y₁])))) ∧
          (c.1.snd, c₂) ∈ Set.range (fun y₂ : Bh =>
            (b y₂, push b m (ind σ k m (Strat.full _ m) (l.map Fib.snd ++ [x.snd, y₂])))) ∧
          c.2 = pb g h m c₁ c₂} := by
      intro x
      apply Set.ext
      intro c
      constructor
      · rintro ⟨y, rfl⟩
        refine ⟨_, _, ⟨y.fst, rfl⟩, ⟨y.snd, rfl⟩, ?_⟩
        show push (fibMap a b g h) m (ind σ k m (Strat.full _ m) (l ++ [x, y])) = _
        rw [ih]
        simp
      · rintro ⟨c₁, c₂, ⟨y₁, h1⟩, ⟨y₂, h2⟩, h3⟩
        obtain ⟨c1, c2⟩ := c
        have h1a : a y₁ = c1.fst := congrArg Prod.fst h1
        have h1b : push a m (ind σ k m (Strat.full _ m) (l.map Fib.fst ++ [x.fst, y₁])) = c₁ :=
          congrArg Prod.snd h1
        have h2a : b y₂ = c1.snd := congrArg Prod.fst h2
        have h2b : push b m (ind σ k m (Strat.full _ m) (l.map Fib.snd ++ [x.snd, y₂])) = c₂ :=
          congrArg Prod.snd h2
        have h3' : c2 = pb g h m c₁ c₂ := h3
        have hy : (g ∘ a) y₁ = (h ∘ b) y₂ := by
          show g (a y₁) = h (b y₂)
          rw [h1a, h2a]
          exact c1.eq
        refine ⟨⟨y₁, y₂, hy⟩, ?_⟩
        refine Prod.ext (Fib.ext h1a h2a) ?_
        show push (fibMap a b g h) m (ind σ k m (Strat.full _ m) (l ++ [x, ⟨y₁, y₂, hy⟩])) = c2
        rw [ih, h3', ← h1b, ← h2b]
        simp
    funext x'
    apply Set.ext
    intro q
    constructor
    · intro hq
      rw [push_ind_full_succ] at hq
      obtain ⟨x, rfl, rfl⟩ := hq
      refine ⟨_, ?_, _, ?_, key x⟩
      · show _ ∈ push a (m + 1) (ind σ k (m + 1) (Strat.full _ (m + 1)) (l.map Fib.fst)) (a x.fst)
        rw [push_ind_full_succ]
        exact ⟨x.fst, rfl, rfl⟩
      · show _ ∈ push b (m + 1) (ind σ k (m + 1) (Strat.full _ (m + 1)) (l.map Fib.snd)) (b x.snd)
        rw [push_ind_full_succ]
        exact ⟨x.snd, rfl, rfl⟩
    · rintro ⟨p₁, hp₁, p₂, hp₂, rfl⟩
      rw [push_ind_full_succ] at hp₁ hp₂
      obtain ⟨x₁, hx₁, rfl⟩ := hp₁
      obtain ⟨x₂, hx₂, rfl⟩ := hp₂
      have hx : (g ∘ a) x₁ = (h ∘ b) x₂ := by
        show g (a x₁) = h (b x₂)
        rw [hx₁, hx₂]
        exact x'.eq
      rw [push_ind_full_succ]
      exact ⟨⟨x₁, x₂, hx⟩, Fib.ext hx₁ hx₂, (key ⟨x₁, x₂, hx⟩).symm⟩

end Pullback

section Tree

variable (T : CoDecomp σ)

/-- The restriction map `G[t] → G[c] ×_{G_e} lim(T|_{S})`, where `S` is the rest of the subtree. -/
def split {r t : Fin T.b} {e : Fin T.m} (he : T.IsChildEdge r t e)
    (hS : t ∈ T.subtree r t \ T.subtree r (T.child e t)) (x : T.PartialLim r t) :
    Fib (T.edgeMap e (T.child e t) he.child_mem ∘ T.partialProj r (T.child e t))
      (T.edgeMap e t he.top_mem ∘
        CoDecomp.LimOn.proj (S := T.subtree r t \ T.subtree r (T.child e t)) t hS) :=
  ⟨restrict T (subtree_child_subset T he) x, restrict T Set.sdiff_subset x,
    edgeMap_compat T x e (T.child e t) t he.child_mem he.top_mem
      (subtree_child_subset T he (T.mem_subtree_self r _)) (T.mem_subtree_self r t)
      (adj_child T he).ne'⟩

theorem split_holds {r t : Fin T.b} {e : Fin T.m} (he : T.IsChildEdge r t e)
    (hS : t ∈ T.subtree r t \ T.subtree r (T.child e t)) (i : Fin σ.r)
    (args : Fin (σ.ar i) → T.PartialLim r t) :
    σ.holds i (split T he hS ∘ args) ↔ σ.holds i args := by
  classical
  show ((∀ s : T.subtree r (T.child e t), σ.holds i (fun j => (args j).val ⟨s.1, _⟩)) ∧
      (∀ s : (T.subtree r t \ T.subtree r (T.child e t) : Set (Fin T.b)),
        σ.holds i (fun j => (args j).val ⟨s.1, _⟩))) ↔
    (∀ s : T.subtree r t, σ.holds i (fun j => (args j).val s))
  constructor
  · rintro ⟨h1, h2⟩ s
    by_cases hs : s.1 ∈ T.subtree r (T.child e t)
    · exact h1 ⟨s.1, hs⟩
    · exact h2 ⟨s.1, ⟨s.2, hs⟩⟩
  · intro h
    exact ⟨fun s => h ⟨s.1, _⟩, fun s => h ⟨s.1, _⟩⟩

theorem split_surj {r t : Fin T.b} {e : Fin T.m} (he : T.IsChildEdge r t e)
    (hS : t ∈ T.subtree r t \ T.subtree r (T.child e t)) :
    Function.Surjective (split T he hS) := by
  classical
  intro z
  have hz : T.edgeMap e (T.child e t) he.child_mem
      (z.fst.val ⟨T.child e t, T.mem_subtree_self r _⟩) =
        T.edgeMap e t he.top_mem (z.snd.val ⟨t, hS⟩) := z.eq
  let v : (s : T.subtree r t) → Fin (T.bag s).n := fun s =>
    if h : s.1 ∈ T.subtree r (T.child e t) then z.fst.val ⟨s.1, h⟩
    else z.snd.val ⟨s.1, ⟨s.2, h⟩⟩
  have hv1 : ∀ (s : Fin T.b) (hs : s ∈ T.subtree r t) (h : s ∈ T.subtree r (T.child e t)),
      v ⟨s, hs⟩ = z.fst.val ⟨s, h⟩ := fun s hs h => dif_pos h
  have hv2 : ∀ (s : Fin T.b) (hs : s ∈ T.subtree r t) (h : s ∉ T.subtree r (T.child e t)),
      v ⟨s, hs⟩ = z.snd.val ⟨s, ⟨hs, h⟩⟩ := fun s hs h => dif_neg h
  have hcompat : ∀ (e' : Fin T.m) (h₁ : (T.ends e').1 ∈ T.subtree r t)
      (h₂ : (T.ends e').2 ∈ T.subtree r t),
      T.gl e' (v ⟨_, h₁⟩) = T.gr e' (v ⟨_, h₂⟩) := by
    intro e' h₁ h₂
    by_cases k₁ : (T.ends e').1 ∈ T.subtree r (T.child e t) <;>
      by_cases k₂ : (T.ends e').2 ∈ T.subtree r (T.child e t)
    · rw [hv1 _ h₁ k₁, hv1 _ h₂ k₂]
      exact z.fst.compat e' k₁ k₂
    · obtain ⟨c1, c2⟩ := cross_child T he (graph_adj T e') k₁ k₂
      have hee : e' = e := cross_edge T he (Or.inl ⟨c1, c2⟩)
      subst hee
      rw [hv1 _ h₁ k₁, hv2 _ h₂ k₂]
      rw [edgeMap_val_fst T z.fst e' _ he.child_mem _ c1.symm k₁,
        edgeMap_val_snd T z.snd e' _ he.top_mem _ c2.symm ⟨h₂, k₂⟩] at hz
      exact hz
    · obtain ⟨c1, c2⟩ := cross_child T he (graph_adj T e').symm k₂ k₁
      have hee : e' = e := cross_edge T he (Or.inr ⟨c1, c2⟩)
      subst hee
      rw [hv2 _ h₁ k₁, hv1 _ h₂ k₂]
      rw [edgeMap_val_snd T z.fst e' _ he.child_mem _ c1.symm k₂,
        edgeMap_val_fst T z.snd e' _ he.top_mem _ c2.symm ⟨h₁, k₁⟩] at hz
      exact hz.symm
    · rw [hv2 _ h₁ k₁, hv2 _ h₂ k₂]
      exact z.snd.compat e' ⟨h₁, k₁⟩ ⟨h₂, k₂⟩
  refine ⟨⟨v, hcompat⟩, ?_⟩
  apply Fib.ext
  · apply CoDecomp.LimOn.ext
    funext s
    exact hv1 s.1 _ s.2
  · apply CoDecomp.LimOn.ext
    funext s
    exact hv2 s.1 _ s.2.2

/-- The projection of the one-node limit to its bag. -/
theorem single_holds (t : Fin T.b) (i : Fin σ.r) (args : Fin (σ.ar i) → T.LimOn {t}) :
    σ.holds i (CoDecomp.LimOn.proj (S := {t}) t rfl ∘ args) ↔ σ.holds i args := by
  show σ.holds i (fun j => (args j).val ⟨t, rfl⟩) ↔
    ∀ s : ({t} : Set (Fin T.b)), σ.holds i (fun j => (args j).val s)
  constructor
  · rintro h ⟨s, hs⟩
    have hs' : s = t := hs
    subst hs'
    exact h
  · intro h
    exact h ⟨t, rfl⟩

theorem single_surj (t : Fin T.b) :
    Function.Surjective (CoDecomp.LimOn.proj (T := T) (S := {t}) t rfl) := by
  intro y
  refine ⟨⟨fun s => (show t = s.1 from (Set.mem_singleton_iff.1 s.2).symm) ▸ y, ?_⟩, rfl⟩
  intro e h₁ h₂
  have a1 : (T.ends e).1 = t := h₁
  have a2 : (T.ends e).2 = t := h₂
  exact absurd (a1.trans a2.symm) (T.ends_ne e)

end Tree

end Obs

open Obs TreeAux in
theorem obs579 {σ : Sig} :
    (∀ (Ah Bh P Q K : Type) [σ.lang.Structure Ah] [σ.lang.Structure Bh]
      (a : Ah → P) (b : Bh → Q) (g : P → K) (h : Q → K) (k m : ℕ)
      (l : List (Fib (g ∘ a) (h ∘ b))),
      push (σ := σ) (k := k)
          (fun z : Fib (g ∘ a) (h ∘ b) => (⟨a z.fst, b z.snd, z.eq⟩ : Fib g h)) m
          (ind σ k m (Strat.full _ m) l) =
        pb g h m
          (push a m (ind σ k m (Strat.full _ m) (l.map Fib.fst)))
          (push b m (ind σ k m (Strat.full _ m) (l.map Fib.snd)))) ∧
    (∀ (T : CoDecomp σ) (r t : Fin T.b) (e : Fin T.m) (he : T.IsChildEdge r t e)
      (hS : t ∈ T.subtree r t \ T.subtree r (T.child e t)) (k m : ℕ),
      push (T.partialProj r t) m (ind σ k m (Strat.full _ m) []) =
        push (Fib.snd :
            Fib (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) →
              Fin (T.bag t).n) m
          (pb (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) m
            (push (T.partialProj r (T.child e t)) m (ind σ k m (Strat.full _ m) []))
            (push (CoDecomp.LimOn.proj t hS) m (ind σ k m (Strat.full _ m) [])))) ∧
    (∀ (T : CoDecomp σ) (t : Fin T.b) (k m : ℕ),
      push (CoDecomp.LimOn.proj (S := {t}) t rfl) m (ind σ k m (Strat.full _ m) []) =
        ind σ k m (Strat.full _ m) []) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Ah Bh P Q K _ _ a b g h k m l
    exact pb_full a b g h k m l
  · intro T r t e he hS k m
    have h1 := pb_full (σ := σ) (T.partialProj r (T.child e t))
      (CoDecomp.LimOn.proj (S := T.subtree r t \ T.subtree r (T.child e t)) t hS)
      (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) k m []
    have h2 := push_ind_full (σ := σ) (split T he hS) (split_holds T he hS) (split_surj T he hS)
      k m []
    simp only [List.map_nil] at h1 h2
    rw [← h1, ← h2, push_push, push_push]
    rfl
  · intro T t k m
    have h := push_ind_full (σ := σ) (CoDecomp.LimOn.proj (T := T) (S := {t}) t rfl)
      (single_holds T t) (single_surj T t) k m []
    simp only [List.map_nil] at h
    exact h

end CoDecompFO

open CoDecompFO FirstOrder

theorem solution {σ : Sig} :
    (∀ (Ah Bh P Q K : Type) [σ.lang.Structure Ah] [σ.lang.Structure Bh]
      (a : Ah → P) (b : Bh → Q) (g : P → K) (h : Q → K) (k m : ℕ)
      (l : List (Fib (g ∘ a) (h ∘ b))),
      push (σ := σ) (k := k)
          (fun z : Fib (g ∘ a) (h ∘ b) => (⟨a z.fst, b z.snd, z.eq⟩ : Fib g h)) m
          (ind σ k m (Strat.full _ m) l) =
        pb g h m
          (push a m (ind σ k m (Strat.full _ m) (l.map Fib.fst)))
          (push b m (ind σ k m (Strat.full _ m) (l.map Fib.snd)))) ∧
    (∀ (T : CoDecomp σ) (r t : Fin T.b) (e : Fin T.m) (he : T.IsChildEdge r t e)
      (hS : t ∈ T.subtree r t \ T.subtree r (T.child e t)) (k m : ℕ),
      push (T.partialProj r t) m (ind σ k m (Strat.full _ m) []) =
        push (Fib.snd :
            Fib (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) →
              Fin (T.bag t).n) m
          (pb (T.edgeMap e (T.child e t) he.child_mem) (T.edgeMap e t he.top_mem) m
            (push (T.partialProj r (T.child e t)) m (ind σ k m (Strat.full _ m) []))
            (push (CoDecomp.LimOn.proj t hS) m (ind σ k m (Strat.full _ m) [])))) ∧
    (∀ (T : CoDecomp σ) (t : Fin T.b) (k m : ℕ),
      push (CoDecomp.LimOn.proj (S := {t}) t rfl) m (ind σ k m (Strat.full _ m) []) =
        ind σ k m (Strat.full _ m) []) :=
  CoDecompFO.obs579
