-- Prove2me | solution 1 for DreyfusWagner.Steiner.theorem1_branch_isSteinerTree
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T10:30:43.999107+00:00
-- url     : https://prove2.me/submissions/3306bc85-4907-4430-9be8-4b3326b177b8

import Theorems.Thm_DreyfusWagner_Steiner_steinerTree_isAcyclic
import Theorems.Thm_DreyfusWagner_Steiner_steinerLength_pair_eq_pathDist
import Definitions.Def_DreyfusWagner_Steiner_Branch
import Definitions.Def_DreyfusWagner_Steiner_AlgorithmA


open Finset SimpleGraph

namespace DreyfusWagner.Steiner.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev graph (S : Finset (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 V))

lemma edge_mem {S : Finset (Sym2 V)} {u v : V} (p : (graph S).Walk u v)
    {e : Sym2 V} (he : e ∈ p.edges) : e ∈ S := by
  have h := p.edges_subset_edgeSet he
  rw [SimpleGraph.edgeSet_fromEdgeSet] at h
  exact h.1

lemma reach_of_edges {H : SimpleGraph V} {S : Finset (Sym2 V)} {u v : V}
    (p : H.Walk u v) (hp : ∀ e ∈ p.edges, e ∈ S) : (graph S).Reachable u v := by
  refine ⟨p.transfer _ ?_⟩
  intro e he
  rw [SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨hp e he, ?_⟩
  rw [Sym2.mem_diagSet]
  exact H.not_isDiag_of_mem_edgeSet (p.edges_subset_edgeSet he)

lemma reach_mono {S T : Finset (Sym2 V)} (hst : S ⊆ T) {u v : V}
    (h : (graph S).Reachable u v) : (graph T).Reachable u v := by
  obtain ⟨p⟩ := h
  exact reach_of_edges p (fun e he => hst (edge_mem p he))

lemma connects_mono {S T : Finset (Sym2 V)} {X Y : Finset V}
    (hst : S ⊆ T) (hxy : X ⊆ Y) (h : Connects S Y) : Connects T X :=
  fun _ hu _ hv => reach_mono hst (h _ (hxy hu) _ (hxy hv))

lemma connects_of_root {S : Finset (Sym2 V)} {Y : Finset V} (x : V)
    (h : ∀ y ∈ Y, (graph S).Reachable x y) : Connects S (insert x Y) := by
  have hr : ∀ y ∈ insert x Y, (graph S).Reachable x y := by
    intro y hy
    rcases mem_insert.mp hy with rfl | hy
    · exact .refl _
    · exact h y hy
  exact fun u hu v hv => (hr u hu).symm.trans (hr v hv)

lemma connects_union {A B : Finset (Sym2 V)} {X Y : Finset V} {x : V}
    (hA : Connects A (insert x X)) (hB : Connects B (insert x Y)) :
    Connects (A ∪ B) (insert x (X ∪ Y)) := by
  apply connects_of_root x
  intro y hy
  rcases mem_union.mp hy with hy | hy
  · exact reach_mono subset_union_left (hA x (by simp) y (by simp [hy]))
  · exact reach_mono subset_union_right (hB x (by simp) y (by simp [hy]))

lemma first_edge_eq_of_common_vertex {H : SimpleGraph V} (hH : H.IsAcyclic)
    {x y z v : V} {p : H.Walk x y} {q : H.Walk x z} (hp : p.IsPath) (hq : q.IsPath)
    (hvp : v ∈ p.support) (hvq : v ∈ q.support) (hv : v ≠ x) :
    p.edges.head? = q.edges.head? := by
  have heq : p.takeUntil v hvp = q.takeUntil v hvq :=
    Subtype.mk.inj (hH.subsingleton_path x v |>.elim
      ⟨_, hp.takeUntil hvp⟩ ⟨_, hq.takeUntil hvq⟩)
  have hsnd : p.snd = q.snd := by
    have hh := congrArg SimpleGraph.Walk.snd heq
    simpa only [SimpleGraph.Walk.snd_takeUntil hv] using hh
  cases p with
  | nil => simp at hvp; exact (hv hvp).elim
  | cons h p =>
    cases q with
    | nil => simp at hvq; exact (hv hvq).elim
    | cons h' q => simpa using congrArg (fun t => some s(x, t)) hsnd

lemma first_edge_eq_of_common_edge {H : SimpleGraph V} (hH : H.IsAcyclic)
    {x y z : V} {p : H.Walk x y} {q : H.Walk x z} (hp : p.IsPath) (hq : q.IsPath)
    {e : Sym2 V} (hep : e ∈ p.edges) (heq : e ∈ q.edges) :
    p.edges.head? = q.edges.head? := by
  obtain ⟨u, v⟩ := e
  by_cases hu : u = x
  · subst u
    exact first_edge_eq_of_common_vertex hH hp hq
      (p.snd_mem_support_of_mem_edges hep) (q.snd_mem_support_of_mem_edges heq)
      (p.adj_of_mem_edges hep).ne'
  · exact first_edge_eq_of_common_vertex hH hp hq
      (p.fst_mem_support_of_mem_edges hep) (q.fst_mem_support_of_mem_edges heq) hu

open Classical in
noncomputable def span (S : Finset (Sym2 V)) (x : V) (Y : Finset V) : Finset (Sym2 V) :=
  S.filter fun e => ∃ y ∈ Y, ∃ p : (graph S).Walk x y, p.IsPath ∧ e ∈ p.edges

lemma span_subset (S : Finset (Sym2 V)) (x : V) (Y : Finset V) : span S x Y ⊆ S := by
  classical
  exact filter_subset _ _

lemma span_connects {S : Finset (Sym2 V)} {x : V} {Y : Finset V}
    (hr : ∀ y ∈ Y, (graph S).Reachable x y) : Connects (span S x Y) (insert x Y) := by
  classical
  apply connects_of_root x
  intro y hy
  obtain ⟨p⟩ := hr y hy
  exact reach_of_edges p.bypass (fun e he =>
    mem_filter.mpr ⟨edge_mem p.bypass he, y, hy, p.bypass, p.bypass_isPath, he⟩)

lemma span_union (S : Finset (Sym2 V)) (x : V) (Y Z : Finset V) :
    span S x (Y ∪ Z) = span S x Y ∪ span S x Z := by
  classical
  ext e
  simp only [span, mem_filter, mem_union]
  constructor
  · rintro ⟨he, y, hy | hy, p, hp, hep⟩
    · exact Or.inl ⟨he, y, hy, p, hp, hep⟩
    · exact Or.inr ⟨he, y, hy, p, hp, hep⟩
  · rintro (⟨he, y, hy, p, hp, hep⟩ | ⟨he, y, hy, p, hp, hep⟩)
    · exact ⟨he, y, Or.inl hy, p, hp, hep⟩
    · exact ⟨he, y, Or.inr hy, p, hp, hep⟩

lemma essential_edge (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) {Y : Finset V} {S : Finset (Sym2 V)}
    (hS : IsSteinerTree G ℓ Y S) {e : Sym2 V} (he : e ∈ S) :
    ¬ Connects (S.erase e) Y := by
  intro hc
  have hle := hS.2.2 (S.erase e) ((erase_subset e S).trans hS.1) hc
  have hp := hpos e (by simpa using hS.1 he)
  unfold arcLength at hle
  have hs := add_sum_erase S ℓ he
  linarith

lemma span_eq (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) {Y : Finset V} {S : Finset (Sym2 V)}
    (hS : IsSteinerTree G ℓ Y S) {x : V} (hr : ∀ y ∈ Y, (graph S).Reachable x y) :
    span S x Y = S := by
  classical
  apply Subset.antisymm (span_subset _ _ _)
  intro e he
  by_contra hn
  apply essential_edge G ℓ hpos hS he
  apply connects_mono (T := S.erase e) (h := span_connects hr)
  · intro f hf
    exact mem_erase.mpr ⟨fun h => hn (h ▸ hf), span_subset _ _ _ hf⟩
  · exact subset_insert _ _

lemma root_reachable (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) {Y : Finset V} {S : Finset (Sym2 V)}
    (hS : IsSteinerTree G ℓ Y S) {x : V} (hx : ∃ e ∈ S, x ∈ e) :
    ∀ y ∈ Y, (graph S).Reachable x y := by
  classical
  obtain ⟨e, he, hxe⟩ := hx
  have hn := essential_edge G ℓ hpos hS he
  unfold Connects at hn
  push Not at hn
  obtain ⟨a, ha, b, hb, hab⟩ := hn
  obtain ⟨p⟩ := hS.2.1 a ha b hb
  have hep : e ∈ p.edges := by
    by_contra hn
    apply hab
    exact reach_of_edges p (fun f hf => mem_erase.mpr
      ⟨fun h => hn (h ▸ hf), edge_mem p hf⟩)
  have hxp : x ∈ p.support := SimpleGraph.Walk.mem_support_of_mem_edges hep hxe
  intro y hy
  exact (p.takeUntil x hxp).reachable.symm.trans (hS.2.1 a ha y hy)

end DreyfusWagner.Steiner.Proof


open Finset SimpleGraph

namespace DreyfusWagner.Steiner.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma length_union_le (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (A B : Finset (Sym2 V)) (hA : A ⊆ G.edgeFinset) :
    arcLength ℓ (A ∪ B) ≤ arcLength ℓ A + arcLength ℓ B := by
  have hn : 0 ≤ ∑ e ∈ A ∩ B, ℓ e :=
    sum_nonneg (fun e he => (hpos e (by simpa using hA (mem_inter.mp he).1)).le)
  have hu := sum_union_inter (f := ℓ) (s₁ := A) (s₂ := B)
  unfold arcLength
  linarith

lemma partition_steiner (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) {Y X Z : Finset V} {S A B : Finset (Sym2 V)}
    {x : V} (hS : IsSteinerTree G ℓ Y S) (heq : S = A ∪ B) (hdis : Disjoint A B)
    (hA : Connects A (insert x X)) (hB : Connects B (insert x Z))
    (hcover : Y ⊆ insert x (X ∪ Z)) : IsSteinerTree G ℓ (insert x X) A := by
  have hAG : A ⊆ G.edgeFinset := by
    intro e he
    apply hS.1
    rw [heq]
    exact mem_union_left _ he
  have hBG : B ⊆ G.edgeFinset := by
    intro e he
    apply hS.1
    rw [heq]
    exact mem_union_right _ he
  refine ⟨hAG, hA, ?_⟩
  intro P hPG hP
  have hcon : Connects (P ∪ B) Y :=
    connects_mono Subset.rfl hcover (connects_union hP hB)
  have hmin := hS.2.2 (P ∪ B) (union_subset hPG hBG) hcon
  have hle := length_union_le G ℓ hpos P B hPG
  have hlen : arcLength ℓ S = arcLength ℓ A + arcLength ℓ B := by
    simp only [heq, arcLength, sum_union hdis]
  linarith

lemma empty_steiner (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (x : V) : IsSteinerTree G ℓ {x} ∅ := by
  refine ⟨empty_subset _, ?_, ?_⟩
  · intro u hu v hv
    simp only [mem_singleton] at hu hv
    subst u; subst v
    exact .refl x
  · intro P hP _
    simp only [arcLength, sum_empty]
    exact sum_nonneg (fun e he => (hpos e (by simpa using hP he)).le)

lemma reachVia_subset (Y : Finset V) (S : Finset (Sym2 V)) (x : V) (C : Finset (Sym2 V)) :
    reachVia Y S x C ⊆ Y := by
  classical
  exact filter_subset _ _

lemma root_not_reachVia (Y : Finset V) (S : Finset (Sym2 V)) (x : V)
    (C : Finset (Sym2 V)) : x ∉ reachVia Y S x C := by
  classical
  rintro hx
  obtain ⟨_, p, hp, e, he, hhead⟩ := mem_filter.mp hx
  have hp0 : p = .nil := SimpleGraph.Walk.isPath_iff_eq_nil.mp hp
  simp [hp0] at hhead

lemma spans_disjoint (S : Finset (Sym2 V)) (Y : Finset V) (x : V)
    (C : Finset (Sym2 V)) (hH : (graph S).IsAcyclic) :
    Disjoint (span S x (reachVia Y S x C)) (span S x (Y \ reachVia Y S x C)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heA heB
  obtain ⟨_, y, hy, p, hp, hep⟩ := mem_filter.mp heA
  obtain ⟨_, z, hz, q, hq, heq⟩ := mem_filter.mp heB
  obtain ⟨_, p₀, hp₀, f, hf, hhead⟩ := mem_filter.mp hy
  have hpp : p = p₀ := Subtype.mk.inj
    (hH.subsingleton_path x y |>.elim ⟨p, hp⟩ ⟨p₀, hp₀⟩)
  have hheads := first_edge_eq_of_common_edge hH hp hq hep heq
  have hqhead : q.edges.head? = some f := by rw [← hheads, hpp]; exact hhead
  apply (mem_sdiff.mp hz).2
  exact mem_filter.mpr ⟨(mem_sdiff.mp hz).1, q, hq, f, hf, hqhead⟩

lemma branch_steiner_of_root (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) {Y : Finset V} {S : Finset (Sym2 V)}
    (hS : IsSteinerTree G ℓ Y S) {x : V} (hr : ∀ y ∈ Y, (graph S).Reachable x y)
    (hH : (graph S).IsAcyclic) (C : Finset (Sym2 V)) :
    IsSteinerTree G ℓ (insert x (reachVia Y S x C)) (branchArcs Y S x C) := by
  classical
  let R := reachVia Y S x C
  have hRY : R ⊆ Y := reachVia_subset _ _ _ _
  have hun : R ∪ (Y \ R) = Y := union_sdiff_of_subset hRY
  have heq : S = span S x R ∪ span S x (Y \ R) := by
    rw [← span_union, hun, span_eq G ℓ hpos hS hr]
  have hA := span_connects (S := S) (x := x) (Y := R) (fun y hy => hr y (hRY hy))
  have hB := span_connects (S := S) (x := x) (Y := Y \ R)
    (fun y hy => hr y (mem_sdiff.mp hy).1)
  exact partition_steiner G ℓ hpos hS heq (spans_disjoint S Y x C hH) hA hB
    (by rw [hun]; exact subset_insert _ _)

end DreyfusWagner.Steiner.Proof

open DreyfusWagner.Steiner DreyfusWagner.Steiner.Proof

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (S : Finset (Sym2 V)) (hS : IsSteinerTree G ℓ Y S)
    (x : V) (hx : ∃ e ∈ S, x ∈ e) (C : Finset (Sym2 V)) (hC : C ⊆ touchingArcs S x) :
    IsSteinerTree G ℓ (insert x (reachVia Y S x C)) (branchArcs Y S x C) := by
  exact branch_steiner_of_root G ℓ hpos hS (root_reachable G ℓ hpos hS hx)
    (steinerTree_isAcyclic G ℓ hpos hconn Y S hS) C

#print axioms solution
