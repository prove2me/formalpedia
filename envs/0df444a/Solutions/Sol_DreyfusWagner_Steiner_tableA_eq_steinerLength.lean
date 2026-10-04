-- Prove2me | solution 1 for DreyfusWagner.Steiner.tableA_eq_steinerLength
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T10:42:45.31524+00:00
-- url     : https://prove2.me/submissions/f42a8c97-aee2-4306-9805-85bc139a296c

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

theorem branch_solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (S : Finset (Sym2 V)) (hS : IsSteinerTree G ℓ Y S)
    (x : V) (hx : ∃ e ∈ S, x ∈ e) (C : Finset (Sym2 V)) (hC : C ⊆ touchingArcs S x) :
    IsSteinerTree G ℓ (insert x (reachVia Y S x C)) (branchArcs Y S x C) := by
  exact branch_steiner_of_root G ℓ hpos hS (root_reachable G ℓ hpos hS hx)
    (steinerTree_isAcyclic G ℓ hpos hconn Y S hS) C



open Finset SimpleGraph

namespace DreyfusWagner.Steiner.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma rooted_partition (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) {Y : Finset V} {S : Finset (Sym2 V)}
    (hS : IsSteinerTree G ℓ Y S) {x : V} (hr : ∀ y ∈ Y, (graph S).Reachable x y)
    (hH : (graph S).IsAcyclic) (C : Finset (Sym2 V)) :
    let R := reachVia Y S x C
    let A := span S x R
    let B := span S x (Y \ R)
    S = A ∪ B ∧ Disjoint A B ∧
      IsSteinerTree G ℓ (insert x R) A ∧ IsSteinerTree G ℓ (insert x (Y \ R)) B := by
  classical
  dsimp only
  let R := reachVia Y S x C
  have hun : R ∪ (Y \ R) = Y := union_sdiff_of_subset (reachVia_subset _ _ _ _)
  have heq : S = span S x R ∪ span S x (Y \ R) := by
    rw [← span_union, hun, span_eq G ℓ hpos hS hr]
  have hd := spans_disjoint S Y x C hH
  have hA := span_connects (S := S) (x := x) (Y := R)
    (fun y hy => hr y (reachVia_subset _ _ _ _ hy))
  have hB := span_connects (S := S) (x := x) (Y := Y \ R)
    (fun y hy => hr y (mem_sdiff.mp hy).1)
  refine ⟨heq, hd, branch_steiner_of_root G ℓ hpos hS hr hH C, ?_⟩
  apply partition_steiner G ℓ hpos hS (heq.trans (union_comm _ _)) hd.symm hB hA
  rw [union_comm, hun]
  exact subset_insert _ _

lemma singleton_connects {q r : V} (hqr : q ≠ r) :
    Connects ({s(q, r)} : Finset (Sym2 V)) {r, q} := by
  apply connects_of_root r
  intro y hy
  have : y = q := mem_singleton.mp hy
  subst y
  apply SimpleGraph.Adj.reachable
  simp [graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq_iff, hqr, hqr.symm]

lemma reachable_after_first {Y : Finset V} {S : Finset (Sym2 V)} {q r z : V}
    (hqr : q ≠ r) (hz : z ∈ reachVia Y S q {s(q, r)}) :
    (graph (S.erase s(q, r))).Reachable r z := by
  classical
  obtain ⟨_, p, hp, e, he, hhead⟩ := mem_filter.mp hz
  have heq : e = s(q, r) := mem_singleton.mp he
  subst e
  cases p with
  | nil => simp at hhead
  | @cons a b c hab p =>
    have hb : b = r := by
      simpa [Sym2.eq_iff, hqr] using hhead
    subst b
    have hn : s(q, r) ∉ p.edges :=
      (List.nodup_cons.mp (show (s(q, r) :: p.edges).Nodup from hp.isTrail.edges_nodup)).1
    exact reach_of_edges p (fun f hf => mem_erase.mpr
      ⟨fun h => hn (h ▸ hf), edge_mem p hf⟩)

lemma edge_removed_steiner (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) {Y : Finset V} {S : Finset (Sym2 V)}
    (hS : IsSteinerTree G ℓ Y S) {q r : V} (hq : q ∈ Y) (hqr : q ≠ r)
    (he : s(q, r) ∈ S) (hR : reachVia Y S q {s(q, r)} = Y.erase q) :
    IsSteinerTree G ℓ {r, q} {s(q, r)} ∧
      IsSteinerTree G ℓ (insert r (Y.erase q)) (S.erase s(q, r)) := by
  classical
  have heq : S = {s(q, r)} ∪ S.erase s(q, r) := by simp [he]
  have hd : Disjoint ({s(q, r)} : Finset (Sym2 V)) (S.erase s(q, r)) := by simp
  have hA := singleton_connects hqr
  have hB := connects_of_root (S := S.erase s(q, r)) r (Y := Y.erase q)
    (fun z hz => reachable_after_first hqr (hR.symm ▸ hz))
  have hcov : Y ⊆ insert r ({q} ∪ Y.erase q) := by
    intro z hz
    by_cases h : z = q
    · simp [h]
    · simp [hz, h]
  refine ⟨partition_steiner G ℓ hpos hS heq hd hA hB hcov, ?_⟩
  exact partition_steiner G ℓ hpos hS (heq.trans (union_comm _ _)) hd.symm hB hA
    (by simpa only [union_comm] using hcov)

lemma optimal_decomposition_aux (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (S : Finset (Sym2 V)) (Y : Finset V) (hS : IsSteinerTree G ℓ Y S)
    (q : V) (hq : q ∈ Y) (hY : 3 ≤ Y.card) :
    ∃ (p : V) (D : Finset V) (S₁ S₂ S₃ : Finset (Sym2 V)),
      D ⊆ Y.erase q ∧ D ≠ Y.erase q ∧ D.Nonempty ∧
      S = S₁ ∪ S₂ ∪ S₃ ∧ Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃ ∧
      IsSteinerTree G ℓ {p, q} S₁ ∧
      IsSteinerTree G ℓ (insert p D) S₂ ∧
      IsSteinerTree G ℓ (insert p (Y.erase q \ D)) S₃ := by
  classical
  induction S using Finset.strongInductionOn generalizing Y q with
  | _ S ih =>
    have hY0 : 2 ≤ (Y.erase q).card := by rw [card_erase_of_mem hq]; omega
    obtain ⟨y, hy⟩ := card_pos.mp (by omega : 0 < (Y.erase q).card)
    have hyq := (mem_erase.mp hy).1
    obtain ⟨w, hw⟩ := (hS.2.1 q hq y (mem_erase.mp hy).2).exists_isPath
    have hwn : ¬w.Nil := fun hn => hyq ((hw.nil_iff_eq.mp hn).symm)
    let r := w.snd
    let e := s(q, r)
    have hqr : q ≠ r := (w.adj_snd hwn).ne
    have he : e ∈ S := edge_mem w (w.mk_start_snd_mem_edges hwn)
    have hyR : y ∈ reachVia Y S q {e} := by
      apply mem_filter.mpr
      refine ⟨(mem_erase.mp hy).2, w, hw, e, by simp, ?_⟩
      dsimp [e, r]
      cases w with
      | nil => exact (hwn (by simp)).elim
      | cons hadj w => simp
    let D := reachVia Y S q {e}
    have hDsub : D ⊆ Y.erase q := by
      intro z hz
      exact mem_erase.mpr ⟨fun h => root_not_reachVia Y S q {e} (by simpa only [h] using hz),
        reachVia_subset _ _ _ _ hz⟩
    have hDne : D.Nonempty := ⟨y, hyR⟩
    by_cases hD : D = Y.erase q
    · have hR : reachVia Y S q {s(q, r)} = Y.erase q := hD
      obtain ⟨hEdge, hRest⟩ := edge_removed_steiner G ℓ hpos hS hq hqr he hR
      have hSS : S = {e} ∪ S.erase e := by simp [he]
      have heRest : e ∉ S.erase e := by simp
      by_cases hr : r ∈ Y.erase q
      · have hproper : ({r} : Finset V) ≠ Y.erase q := by
          intro h
          rw [← h, card_singleton] at hY0
          omega
        refine ⟨r, {r}, {e}, ∅, S.erase e, singleton_subset_iff.mpr hr, hproper,
          singleton_nonempty r, ?_, by simp, by simp, by simp, hEdge, ?_, ?_⟩
        · simpa using hSS
        · simpa using empty_steiner G ℓ hpos r
        · have hsets : insert r (Y.erase q \ {r}) = insert r (Y.erase q) := by
            ext z
            simp only [mem_insert, mem_sdiff, mem_singleton]
            tauto
          simpa only [hsets] using hRest
      · have hsmall : S.erase e ⊂ S := erase_ssubset he
        have hsize : 3 ≤ (insert r (Y.erase q)).card := by
          rw [card_insert_of_notMem hr]
          omega
        obtain ⟨p, E, A, B, C, hEsub, hEne, hEnon, hsplit, hAB, hAC, hBC, hA, hB, hC⟩ :=
          ih (S.erase e) hsmall (insert r (Y.erase q)) hRest r (by simp) hsize
        simp only [erase_insert hr] at hEsub hEne hC
        have hBsmall : B ⊆ S.erase e := by rw [hsplit]; exact (subset_union_right).trans subset_union_left
        have hCsmall : C ⊆ S.erase e := by rw [hsplit]; exact subset_union_right
        have hEB : Disjoint ({e} : Finset (Sym2 V)) B := by
          apply Finset.disjoint_left.mpr
          intro f hf hfb
          have : f = e := mem_singleton.mp hf
          subst f
          exact heRest (hBsmall hfb)
        have hEC : Disjoint ({e} : Finset (Sym2 V)) C := by
          apply Finset.disjoint_left.mpr
          intro f hf hfc
          have : f = e := mem_singleton.mp hf
          subst f
          exact heRest (hCsmall hfc)
        have hnewB : Disjoint ({e} ∪ A) B := Finset.disjoint_union_left.mpr ⟨hEB, hAB⟩
        have hnewC : Disjoint ({e} ∪ A) C := Finset.disjoint_union_left.mpr ⟨hEC, hAC⟩
        have hbig : S = ({e} ∪ A) ∪ B ∪ C := by
          rw [hSS, hsplit]
          simp only [union_assoc]
        have hnewConn : Connects ({e} ∪ A) {p, q} := by
          have hc := connects_union hEdge.2.1 (show Connects A (insert r {p}) from
            by simpa only [Finset.pair_comm] using hA.2.1)
          apply connects_mono Subset.rfl (h := hc)
          intro z hz
          simp only [mem_insert, mem_singleton, mem_union] at hz ⊢
          tauto
        have hpartsConn : Connects (B ∪ C) (insert p (Y.erase q)) := by
          have hc := connects_union hB.2.1 hC.2.1
          simpa only [union_sdiff_of_subset hEsub] using hc
        have hnew : IsSteinerTree G ℓ {p, q} ({e} ∪ A) := by
          apply partition_steiner G ℓ hpos hS
            (hbig.trans (union_assoc _ _ _))
            (Finset.disjoint_union_right.mpr ⟨hnewB, hnewC⟩) hnewConn hpartsConn
          intro z hz
          by_cases hzq : z = q
          · simp [hzq]
          · simp [hz, hzq]
        exact ⟨p, E, {e} ∪ A, B, C, hEsub, hEne, hEnon, hbig,
          hnewB, hnewC, hBC, hnew, hB, hC⟩
    · obtain ⟨heq, hdis, hA, hB⟩ := rooted_partition G ℓ hpos hS
        (fun z hz => hS.2.1 q hq z hz) (steinerTree_isAcyclic G ℓ hpos hconn Y S hS) {e}
      have hsets : insert q (Y \ D) = insert q (Y.erase q \ D) := by
        ext z
        simp only [mem_insert, mem_sdiff, mem_erase]
        tauto
      refine ⟨q, D, ∅, span S q D, span S q (Y \ D), hDsub, hD, hDne, ?_,
        by simp, by simp, hdis, ?_, hA, ?_⟩
      · simpa using heq
      · simpa using empty_steiner G ℓ hpos q
      · change IsSteinerTree G ℓ (insert q (Y \ D)) (span S q (Y \ D)) at hB
        simpa only [hsets] using hB

end DreyfusWagner.Steiner.Proof

open DreyfusWagner.Steiner DreyfusWagner.Steiner.Proof

theorem decomposition_solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (S : Finset (Sym2 V)) (hS : IsSteinerTree G ℓ Y S)
    (q : V) (hq : q ∈ Y) (hY : 3 ≤ Y.card) :
    ∃ (p : V) (D : Finset V) (S₁ S₂ S₃ : Finset (Sym2 V)),
      D ⊆ Y.erase q ∧ D ≠ Y.erase q ∧ D.Nonempty ∧
      S = S₁ ∪ S₂ ∪ S₃ ∧ Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃ ∧
      IsSteinerTree G ℓ {p, q} S₁ ∧
      IsSteinerTree G ℓ (insert p D) S₂ ∧
      IsSteinerTree G ℓ (insert p (Y.erase q \ D)) S₃ := by
  exact optimal_decomposition_aux G ℓ hpos hconn S Y hS q hq hY



open Finset SimpleGraph

namespace DreyfusWagner.Steiner.Proof

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma exists_steiner (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hconn : G.Connected) (X : Finset V) : ∃ S, IsSteinerTree G ℓ X S := by
  classical
  let F := G.edgeFinset.powerset.filter (fun S => Connects S X)
  have hF : F.Nonempty := by
    refine ⟨G.edgeFinset, mem_filter.mpr ⟨mem_powerset.mpr Subset.rfl, ?_⟩⟩
    intro x hx y hy
    obtain ⟨p⟩ := hconn.preconnected x y
    exact reach_of_edges p (fun e he => by simpa using p.edges_subset_edgeSet he)
  obtain ⟨S, hS, hmin⟩ := exists_min_image F (arcLength ℓ) hF
  obtain ⟨hsub, hc⟩ := mem_filter.mp hS
  exact ⟨S, mem_powerset.mp hsub, hc,
    fun T ht hc => hmin T (mem_filter.mpr ⟨mem_powerset.mpr ht, hc⟩)⟩

lemma steiner_le_length (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    {X : Finset V} {S : Finset (Sym2 V)} (hsub : S ⊆ G.edgeFinset) (hc : Connects S X) :
    steinerLength G ℓ X ≤ (arcLength ℓ S : WithTop ℝ) := by
  classical
  exact Finset.inf_le (mem_filter.mpr ⟨mem_powerset.mpr hsub, hc⟩)

lemma steiner_eq_length (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    {X : Finset V} {S : Finset (Sym2 V)} (hS : IsSteinerTree G ℓ X S) :
    steinerLength G ℓ X = (arcLength ℓ S : WithTop ℝ) := by
  classical
  apply le_antisymm (steiner_le_length G ℓ hS.1 hS.2.1)
  apply Finset.le_inf
  intro T hT
  obtain ⟨ht, hc⟩ := mem_filter.mp hT
  exact WithTop.coe_le_coe.mpr (hS.2.2 T (mem_powerset.mp ht) hc)

lemma steiner_singleton (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (x : V) : steinerLength G ℓ {x} = 0 := by
  simpa [arcLength] using steiner_eq_length G ℓ (empty_steiner G ℓ hpos x)

lemma path_self (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected) (x : V) :
    pathDist G ℓ x x = 0 := by
  rw [← steinerLength_pair_eq_pathDist G ℓ hpos hconn]
  simpa using steiner_singleton G ℓ hpos x

lemma finite_inf_attained {α β : Type*} [LinearOrder β] [OrderTop β]
    (s : Finset α) (f : α → β) (hs : s.Nonempty) : ∃ a ∈ s, s.inf f = f a := by
  obtain ⟨a, ha, hm⟩ := exists_min_image s f hs
  exact ⟨a, ha, le_antisymm (Finset.inf_le ha) (Finset.le_inf hm)⟩

lemma all_splits_nonempty (D : Finset V) (hD : 2 ≤ D.card) :
    (D.powerset.filter (fun E => E.Nonempty ∧ E ≠ D)).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := card_pos.mp (by omega : 0 < D.card)
  refine ⟨{x}, mem_filter.mpr ⟨mem_powerset.mpr (singleton_subset_iff.mpr hx),
    singleton_nonempty x, ?_⟩⟩
  intro h
  rw [← h, card_singleton] at hD
  omega

lemma union_candidate_le (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (D E : Finset V) (hE : E ⊆ D) (m k : V) :
    steinerLength G ℓ (insert m D) ≤ pathDist G ℓ m k +
      (steinerLength G ℓ (insert k E) + steinerLength G ℓ (insert k (D \ E))) := by
  classical
  obtain ⟨A, hA⟩ := exists_steiner G ℓ hconn {k, m}
  obtain ⟨B, hB⟩ := exists_steiner G ℓ hconn (insert k E)
  obtain ⟨C, hC⟩ := exists_steiner G ℓ hconn (insert k (D \ E))
  have hd : pathDist G ℓ m k = (arcLength ℓ A : WithTop ℝ) := by
    rw [← steinerLength_pair_eq_pathDist G ℓ hpos hconn, pair_comm m k]
    exact steiner_eq_length G ℓ hA
  rw [hd, steiner_eq_length G ℓ hB, steiner_eq_length G ℓ hC, ← WithTop.coe_add,
    ← WithTop.coe_add]
  have hBC : B ∪ C ⊆ G.edgeFinset := union_subset hB.1 hC.1
  have hcost : arcLength ℓ (A ∪ (B ∪ C)) ≤ arcLength ℓ A + (arcLength ℓ B + arcLength ℓ C) :=
    (length_union_le G ℓ hpos A (B ∪ C) hA.1).trans
      (add_le_add le_rfl (length_union_le G ℓ hpos B C hB.1))
  apply (steiner_le_length G ℓ (union_subset hA.1 hBC) ?_).trans (WithTop.coe_le_coe.mpr hcost)
  have hc := connects_union hA.2.1 (connects_union hB.2.1 hC.2.1)
  apply connects_mono Subset.rfl (h := hc)
  rw [union_sdiff_of_subset hE]
  intro z hz
  simp only [mem_insert, mem_singleton, mem_union] at hz ⊢
  tauto

end DreyfusWagner.Steiner.Proof


open Finset SimpleGraph
open DreyfusWagner.Steiner DreyfusWagner.Steiner.Proof

theorem recurrence_solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (D : Finset V) (hD : 2 ≤ D.card) (m : V) :
    steinerLength G ℓ (insert m D) =
      Finset.univ.inf fun k => pathDist G ℓ m k +
        (D.powerset.filter (fun E => E.Nonempty ∧ E ≠ D)).inf fun E =>
          steinerLength G ℓ (insert k E) + steinerLength G ℓ (insert k (D \ E)) := by
  classical
  apply le_antisymm
  · apply Finset.le_inf
    intro k hk
    obtain ⟨E, hE, heq⟩ := finite_inf_attained
      (D.powerset.filter (fun E => E.Nonempty ∧ E ≠ D))
      (fun E => steinerLength G ℓ (insert k E) + steinerLength G ℓ (insert k (D \ E)))
      (all_splits_nonempty D hD)
    rw [heq]
    exact union_candidate_le G ℓ hpos hconn D E (mem_powerset.mp (mem_filter.mp hE).1) m k
  · by_cases hm : m ∈ D
    · have hproper : ({m} : Finset V) ≠ D := by
        intro h
        rw [← h, card_singleton] at hD
        omega
      have hcand : {m} ∈ D.powerset.filter (fun E => E.Nonempty ∧ E ≠ D) :=
        mem_filter.mpr ⟨mem_powerset.mpr (singleton_subset_iff.mpr hm), singleton_nonempty m, hproper⟩
      apply (Finset.inf_le (mem_univ m)).trans
      apply (add_le_add le_rfl (Finset.inf_le hcand)).trans
      have hsets : insert m (D \ {m}) = insert m D := by
        ext z
        simp only [mem_insert, mem_sdiff, mem_singleton]
        tauto
      simp only [path_self G ℓ hpos hconn, insert_eq_of_mem (mem_singleton_self m), steiner_singleton G ℓ hpos,
        hsets, zero_add, le_refl]
    · obtain ⟨S, hS⟩ := exists_steiner G ℓ hconn (insert m D)
      have hsize : 3 ≤ (insert m D).card := by rw [card_insert_of_notMem hm]; omega
      obtain ⟨p, E, A, B, C, hEsub, hEne, hEnon, hsplit, hAB, hAC, hBC, hA, hB, hC⟩ :=
        optimal_decomposition_aux G ℓ hpos hconn S (insert m D) hS m (by simp) hsize
      simp only [erase_insert hm] at hEsub hEne hC
      have hcand : E ∈ D.powerset.filter (fun E => E.Nonempty ∧ E ≠ D) :=
        mem_filter.mpr ⟨mem_powerset.mpr hEsub, hEnon, hEne⟩
      apply (Finset.inf_le (mem_univ p)).trans
      apply (add_le_add le_rfl (Finset.inf_le hcand)).trans
      have hd : pathDist G ℓ m p = (arcLength ℓ A : WithTop ℝ) := by
        rw [← steinerLength_pair_eq_pathDist G ℓ hpos hconn, pair_comm m p]
        exact steiner_eq_length G ℓ hA
      rw [hd, steiner_eq_length G ℓ hB, steiner_eq_length G ℓ hC, steiner_eq_length G ℓ hS,
        ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      have hcost : arcLength ℓ S = arcLength ℓ A + (arcLength ℓ B + arcLength ℓ C) := by
        rw [hsplit]
        unfold arcLength
        rw [sum_union (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩), sum_union hAB, add_assoc]
      exact le_of_eq hcost.symm



open Finset SimpleGraph
open DreyfusWagner.Steiner DreyfusWagner.Steiner.Proof

namespace DreyfusWagner.Steiner.Proof

lemma inf_splits_eq_all {V : Type*} [LinearOrder V] (D : Finset V) (hD : D.Nonempty)
    (f : Finset V → WithTop ℝ) (hsym : ∀ E ⊆ D, f E = f (D \ E)) :
    (splits D).inf f = (D.powerset.filter (fun E => E.Nonempty ∧ E ≠ D)).inf f := by
  classical
  apply le_antisymm
  · apply Finset.le_inf
    intro E hE
    obtain ⟨hsub, hne, hproper⟩ := mem_filter.mp hE
    have hsub := mem_powerset.mp hsub
    by_cases hmin : D.min' hD ∈ E
    · exact Finset.inf_le (mem_splits.mpr ⟨hD, hsub, hmin, hproper⟩)
    · have hcomp : D \ E ∈ splits D := by
        refine mem_splits.mpr ⟨hD, sdiff_subset, mem_sdiff.mpr ⟨D.min'_mem hD, hmin⟩, ?_⟩
        intro heq
        obtain ⟨x, hx⟩ := hne
        have hxD : x ∈ D \ E := heq.symm ▸ hsub hx
        exact (mem_sdiff.mp hxD).2 hx
      exact (Finset.inf_le hcomp).trans_eq (hsym E hsub).symm
  · apply Finset.le_inf
    intro E hE
    obtain ⟨hne, hsub, hmin, hproper⟩ := mem_splits.mp hE
    exact Finset.inf_le (mem_filter.mpr ⟨mem_powerset.mpr hsub, ⟨_, hmin⟩, hproper⟩)

end DreyfusWagner.Steiner.Proof

set_option maxHeartbeats 800000 in
theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (D : Finset V) (hD : D.Nonempty) (I : V) :
    tableA (pathDist G ℓ) D I = steinerLength G ℓ (insert I D) := by
  classical
  induction D using Finset.strongInductionOn generalizing I with
  | _ D ih =>
    by_cases hc : D.card ≤ 1
    · have hcard : D.card = 1 := by have := card_pos.mpr hD; omega
      obtain ⟨t, rfl⟩ := card_eq_one.mp hcard
      rw [tableA]
      simpa [pair_comm] using (steinerLength_pair_eq_pathDist G ℓ hpos hconn t I).symm
    · rw [tableA, dif_neg hc, recurrence_solution G ℓ hpos hconn D (by omega) I]
      apply Finset.inf_congr rfl
      intro k hk
      congr 1
      calc
        (splits D).attach.inf (fun E => tableA (pathDist G ℓ) E.1 k +
          tableA (pathDist G ℓ) (D \ E.1) k) =
            (splits D).attach.inf (fun E => steinerLength G ℓ (insert k E.1) +
              steinerLength G ℓ (insert k (D \ E.1))) := by
          apply Finset.inf_congr rfl
          intro E hE
          obtain ⟨hne, hsub, hmin, hproper⟩ := mem_splits.mp E.2
          have hsmall : E.1 ⊂ D := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hproper⟩
          have hcsmall : D \ E.1 ⊂ D := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨sdiff_subset, ?_⟩
            intro heq
            have : D.min' hne ∈ D \ E.1 := heq.symm ▸ D.min'_mem hne
            exact (mem_sdiff.mp this).2 hmin
          have hcne : (D \ E.1).Nonempty := by
            by_contra hempty
            have hrev : D ⊆ E.1 := sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp hempty)
            exact hproper (Subset.antisymm hsub hrev)
          rw [ih E.1 hsmall ⟨_, hmin⟩ k, ih (D \ E.1) hcsmall hcne k]
        _ = (splits D).inf (fun E => steinerLength G ℓ (insert k E) +
              steinerLength G ℓ (insert k (D \ E))) :=
                Finset.inf_attach (splits D) (fun E : Finset V =>
                  steinerLength G ℓ (insert k E) + steinerLength G ℓ (insert k (D \ E)))
        _ = _ := inf_splits_eq_all D hD _ (by
          intro E hE
          have hcomp : D \ (D \ E) = E := by
            ext z
            simp only [mem_sdiff]
            constructor
            · tauto
            · intro hz
              exact ⟨hE hz, fun h => h.2 hz⟩
          rw [hcomp, add_comm])

#print axioms solution
