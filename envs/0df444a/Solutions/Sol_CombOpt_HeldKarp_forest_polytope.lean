-- Prove2me | solution 1 for CombOpt.HeldKarp.forest_polytope
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:02:04.252242+00:00
-- url     : https://prove2.me/submissions/9b4b0332-e9a8-4953-bdd6-dbf07eafeadb

import Mathlib
import Definitions.Def_CombOpt_HeldKarp_Graph_IsForest
import Definitions.Def_CombOpt_HeldKarp_Graph_gamma

open Finset

namespace ForestPolyAux

open CombOpt.HeldKarp

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- The simple graph on `V` spanned by the (non-loop) ends of the edges of `F`. -/
noncomputable def sg (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) : SimpleGraph V := by
  classical
  exact SimpleGraph.fromEdgeSet ((F.image G.ends : Finset (Sym2 V)) : Set (Sym2 V))

lemma sg_adj (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (u v : V) :
    (sg G F).Adj u v ↔ (∃ e ∈ F, G.ends e = s(u, v)) ∧ u ≠ v := by
  classical
  unfold sg
  rw [SimpleGraph.fromEdgeSet_adj]
  simp [Finset.mem_coe, Finset.mem_image]

lemma sg_mono (G : CombOpt.HeldKarp.Graph V E) {F F' : Finset E} (h : F ⊆ F') : sg G F ≤ sg G F' := by
  intro u v huv
  rw [sg_adj] at huv ⊢
  obtain ⟨⟨e, he, hee⟩, hne⟩ := huv
  exact ⟨⟨e, h he, hee⟩, hne⟩

/-- Structural facts about a (custom) forest: no loops, and distinct edges have distinct ends. -/
lemma forest_noLoop (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (hF : G.IsForest F) :
    ∀ e ∈ F, ¬ (G.ends e).IsDiag := by
  intro e he hd
  induction h : G.ends e using Sym2.ind with
  | h a b =>
    rw [h, Sym2.mk_isDiag_iff] at hd
    subst hd
    apply hF
    refine ⟨a, CombOpt.HeldKarp.Graph.Walk.cons e h (CombOpt.HeldKarp.Graph.Walk.nil a), ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [CombOpt.HeldKarp.Graph.Walk.edges]
    · simp [CombOpt.HeldKarp.Graph.Walk.support]
    · simp [CombOpt.HeldKarp.Graph.Walk.edges]
    · intro e' he'
      simp [CombOpt.HeldKarp.Graph.Walk.edges] at he'
      rw [he']; exact he

lemma forest_inj (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (hF : G.IsForest F) :
    ∀ e₁ ∈ F, ∀ e₂ ∈ F, G.ends e₁ = G.ends e₂ → e₁ = e₂ := by
  intro e₁ h₁ e₂ h₂ heq
  by_contra hne
  have hnl := forest_noLoop G F hF e₁ h₁
  induction h : G.ends e₁ using Sym2.ind with
  | h a b =>
    rw [h] at hnl heq
    have hab : a ≠ b := by rwa [Sym2.mk_isDiag_iff] at hnl
    apply hF
    have h2 : G.ends e₂ = s(b, a) := by rw [← heq, Sym2.eq_swap]
    refine ⟨a, CombOpt.HeldKarp.Graph.Walk.cons e₁ h (CombOpt.HeldKarp.Graph.Walk.cons e₂ h2 (CombOpt.HeldKarp.Graph.Walk.nil a)), ⟨?_, ?_, ?_⟩, ?_⟩
    · simp [CombOpt.HeldKarp.Graph.Walk.edges, hne]
    · simp [CombOpt.HeldKarp.Graph.Walk.support, hab]
    · simp [CombOpt.HeldKarp.Graph.Walk.edges]
    · intro e' he'
      simp [CombOpt.HeldKarp.Graph.Walk.edges] at he'
      rcases he' with rfl | rfl
      · exact h₁
      · exact h₂

lemma dropLast_nodup_of_tail {α : Type*} (u : α) (t : List α) (ht : t ≠ [])
    (hlast : t.getLast ht = u) (hnd : t.Nodup) : (u :: t).dropLast.Nodup := by
  have hsplit : t = t.dropLast ++ [u] := by
    conv_lhs => rw [← List.dropLast_append_getLast ht]
    rw [hlast]
  rw [List.dropLast_cons_of_ne_nil ht]
  rw [hsplit] at hnd
  rw [List.nodup_append] at hnd
  refine List.nodup_cons.mpr ⟨?_, hnd.1⟩
  intro hu
  exact hnd.2.2 u hu u (List.mem_singleton_self u) rfl

lemma tail_nodup_of_dropLast {α : Type*} (u : α) (t : List α) (ht : t ≠ [])
    (hlast : t.getLast ht = u) (hnd : (u :: t).dropLast.Nodup) : t.Nodup := by
  have hsplit : t = t.dropLast ++ [u] := by
    conv_lhs => rw [← List.dropLast_append_getLast ht]
    rw [hlast]
  rw [List.dropLast_cons_of_ne_nil ht, List.nodup_cons] at hnd
  rw [hsplit, List.nodup_append]
  refine ⟨hnd.2, List.nodup_singleton u, ?_⟩
  intro a ha b hb hab
  rw [List.mem_singleton] at hb
  subst hb; subst hab
  exact hnd.1 ha

/-- Lift a walk of `sg G F` to a walk of `G` using edges of `F`. -/
noncomputable def liftWalk (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) :
    {u v : V} → (sg G F).Walk u v → CombOpt.HeldKarp.Graph.Walk G u v
  | _, _, .nil => .nil _
  | _, _, .cons h p =>
      .cons (Classical.choose ((sg_adj G F _ _).mp h).1)
        (Classical.choose_spec ((sg_adj G F _ _).mp h).1).2 (liftWalk G F p)

lemma liftWalk_edges (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) {u v : V}
    (p : (sg G F).Walk u v) :
    (liftWalk G F p).edges.map G.ends = p.edges ∧ ∀ e ∈ (liftWalk G F p).edges, e ∈ F := by
  induction p with
  | nil => simp [liftWalk, CombOpt.HeldKarp.Graph.Walk.edges]
  | cons h p ih =>
    simp only [liftWalk, CombOpt.HeldKarp.Graph.Walk.edges, List.map_cons,
      SimpleGraph.Walk.edges_cons, List.mem_cons]
    refine ⟨?_, ?_⟩
    · rw [ih.1, (Classical.choose_spec ((sg_adj G F _ _).mp h).1).2]
    · rintro e (rfl | he)
      · exact (Classical.choose_spec ((sg_adj G F _ _).mp h).1).1
      · exact ih.2 e he

lemma liftWalk_support (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) {u v : V}
    (p : (sg G F).Walk u v) : (liftWalk G F p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [liftWalk, CombOpt.HeldKarp.Graph.Walk.support, SimpleGraph.Walk.support_cons, ih]

/-- A custom forest spans an acyclic simple graph. -/
lemma forest_acyclic (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (hF : G.IsForest F) :
    (sg G F).IsAcyclic := by
  intro v c hc
  apply hF
  obtain ⟨hmap, hmem⟩ := liftWalk_edges G F c
  refine ⟨v, liftWalk G F c, ⟨?_, ?_, ?_⟩, hmem⟩
  · have := hc.edges_nodup
    rw [← hmap] at this
    exact List.Nodup.of_map _ this
  · rw [liftWalk_support]
    have hnn : c.support.tail ≠ [] := by
      intro h
      have h1 := congrArg List.length h
      rw [List.length_tail, SimpleGraph.Walk.length_support] at h1
      have := hc.three_le_length
      simp only [List.length_nil] at h1; omega
    have hsup : c.support = v :: c.support.tail := by
      conv_lhs => rw [← List.cons_head_tail (SimpleGraph.Walk.support_ne_nil c)]
      rw [SimpleGraph.Walk.head_support]
    rw [hsup]
    apply dropLast_nodup_of_tail v _ hnn _ hc.support_nodup
    have h1 := SimpleGraph.Walk.getLast_support c
    rw [← List.getLast_cons hnn (a := v)]
    simp only [← hsup, h1]
  · have := hc.three_le_length
    have hl : (liftWalk G F c).edges.length = c.length := by
      rw [← List.length_map (f := G.ends), hmap, SimpleGraph.Walk.length_edges]
    omega

/-- Push a walk of `G` with edges in a loopless `F` down to `sg G F`. -/
noncomputable def pushWalk (G : CombOpt.HeldKarp.Graph V E) (F : Finset E)
    (hl : ∀ e ∈ F, ¬ (G.ends e).IsDiag) :
    {u v : V} → (p : CombOpt.HeldKarp.Graph.Walk G u v) → (∀ e ∈ p.edges, e ∈ F) →
      (sg G F).Walk u v
  | _, _, .nil _, _ => .nil
  | _, _, .cons e h p, hp =>
      .cons (by
        have he : e ∈ F := hp e (by simp [CombOpt.HeldKarp.Graph.Walk.edges])
        rw [sg_adj]
        refine ⟨⟨e, he, h⟩, ?_⟩
        intro huv
        apply hl e he
        rw [h, huv]; exact Sym2.mk_isDiag_iff.mpr rfl)
        (pushWalk G F hl p (fun e' he' => hp e' (by
          simp [CombOpt.HeldKarp.Graph.Walk.edges, he'])))

lemma pushWalk_edges (G : CombOpt.HeldKarp.Graph V E) (F : Finset E)
    (hl : ∀ e ∈ F, ¬ (G.ends e).IsDiag) {u v : V}
    (p : CombOpt.HeldKarp.Graph.Walk G u v) (hp : ∀ e ∈ p.edges, e ∈ F) :
    (pushWalk G F hl p hp).edges = p.edges.map G.ends := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    simp only [pushWalk, SimpleGraph.Walk.edges_cons, CombOpt.HeldKarp.Graph.Walk.edges,
      List.map_cons, ih, h]

lemma pushWalk_support (G : CombOpt.HeldKarp.Graph V E) (F : Finset E)
    (hl : ∀ e ∈ F, ¬ (G.ends e).IsDiag) {u v : V}
    (p : CombOpt.HeldKarp.Graph.Walk G u v) (hp : ∀ e ∈ p.edges, e ∈ F) :
    (pushWalk G F hl p hp).support = p.support := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    simp only [pushWalk, SimpleGraph.Walk.support_cons, CombOpt.HeldKarp.Graph.Walk.support, ih]

lemma cwalk_support (G : CombOpt.HeldKarp.Graph V E) {u w : V}
    (p : CombOpt.HeldKarp.Graph.Walk G u w) (hp : p.edges ≠ []) :
    ∃ t : List V, p.support = u :: (t ++ [w]) := by
  induction p with
  | nil => simp [CombOpt.HeldKarp.Graph.Walk.edges] at hp
  | @cons a b c e h p ih =>
    cases p with
    | nil => exact ⟨[], by simp [CombOpt.HeldKarp.Graph.Walk.support]⟩
    | cons e' h' p' =>
      obtain ⟨t, ht⟩ := ih (by simp [CombOpt.HeldKarp.Graph.Walk.edges])
      refine ⟨b :: t, ?_⟩
      simp only [CombOpt.HeldKarp.Graph.Walk.support] at ht ⊢
      rw [ht]; simp

/-- Loopless, injectively-labelled, acyclic edge sets are custom forests. -/
lemma isForest_of (G : CombOpt.HeldKarp.Graph V E) (F : Finset E)
    (hl : ∀ e ∈ F, ¬ (G.ends e).IsDiag)
    (hinj : ∀ e₁ ∈ F, ∀ e₂ ∈ F, G.ends e₁ = G.ends e₂ → e₁ = e₂)
    (hac : (sg G F).IsAcyclic) : G.IsForest F := by
  rintro ⟨v, p, ⟨hnd, hsup, hlen⟩, hp⟩
  apply hac (pushWalk G F hl p hp)
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def, pushWalk_edges]
    exact hnd.map_on (fun a ha b hb h => hinj a (hp a ha) b (hp b hb) h)
  · intro h
    have := congrArg SimpleGraph.Walk.length h
    rw [SimpleGraph.Walk.length_nil, ← SimpleGraph.Walk.length_edges, pushWalk_edges,
      List.length_map] at this
    omega
  · rw [pushWalk_support]
    have hpe : p.edges ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen
    obtain ⟨t, ht⟩ := cwalk_support G p hpe
    rw [ht] at hsup ⊢
    simp only [List.tail_cons]
    rw [List.dropLast_cons_of_ne_nil (by simp), List.dropLast_concat, List.nodup_cons] at hsup
    rw [List.nodup_append]
    refine ⟨hsup.2, List.nodup_singleton v, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst hb; subst hab
    exact hsup.1 ha

/-! ### Counting edges -/

open Classical

lemma acyclic_card {W : Type*} [Fintype W] [Nonempty W] (H : SimpleGraph W)
    (h : H.IsAcyclic) : Nat.card H.edgeSet + 1 ≤ Fintype.card W := by
  classical
  obtain ⟨H', hle, hmax⟩ := SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
    (G := (⊤ : SimpleGraph W)) le_top h
  have hmax' : Maximal SimpleGraph.IsAcyclic H' := by
    refine ⟨hmax.1.2, fun K hK hle' => hmax.2 ⟨le_top, hK⟩ hle'⟩
  have htree : H'.IsTree := SimpleGraph.maximal_isAcyclic_iff_isTree.mp hmax'
  have hc := htree.card_edgeFinset
  have hsub : H.edgeFinset ⊆ H'.edgeFinset := SimpleGraph.edgeFinset_mono hle
  have := card_le_card hsub
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  omega

lemma induce_edges_eq (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (S : Set V)
    [DecidableEq V] [Fintype ((sg G F).induce S).edgeSet] :
    (((sg G F).induce S).edgeFinset).map
        ⟨Sym2.map Subtype.val, Sym2.map.injective Subtype.val_injective⟩ =
      (F.filter (fun e => ¬ (G.ends e).IsDiag ∧ ∀ a ∈ G.ends e, a ∈ S)).image G.ends := by
  classical
  ext z
  simp only [mem_map, mem_image, mem_filter, SimpleGraph.mem_edgeFinset,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨w, hw, rfl⟩
    induction w using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj, sg_adj] at hw
      obtain ⟨⟨e, he, hee⟩, hne⟩ := hw
      refine ⟨e, ⟨he, ?_, ?_⟩, ?_⟩
      · rw [hee, Sym2.mk_isDiag_iff]; exact hne
      · intro c hc
        rw [hee, Sym2.mem_iff] at hc
        rcases hc with rfl | rfl
        · exact a.2
        · exact b.2
      · rw [hee]; rfl
  · rintro ⟨e, ⟨he, hnd, hin⟩, rfl⟩
    induction h : G.ends e using Sym2.ind with
    | h a b =>
      rw [h] at hnd hin
      have ha : a ∈ S := hin a (Sym2.mem_mk_left a b)
      have hb : b ∈ S := hin b (Sym2.mem_mk_right a b)
      refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, rfl⟩
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj, sg_adj]
      refine ⟨⟨e, he, h⟩, ?_⟩
      rwa [Sym2.mk_isDiag_iff] at hnd

lemma induce_card_le (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (S : Set V) :
    Nat.card ((sg G F).induce S).edgeSet ≤
      (F.filter (fun e => ∀ a ∈ G.ends e, a ∈ S)).card := by
  classical
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have h := induce_edges_eq G F S
  have h1 := congrArg Finset.card h
  rw [card_map] at h1
  rw [h1]
  refine (card_image_le).trans (card_le_card ?_)
  intro e he
  simp only [mem_filter] at he ⊢
  exact ⟨he.1, he.2.2⟩

lemma induce_card_ge (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (S : Set V)
    (hl : ∀ e ∈ F, ¬ (G.ends e).IsDiag)
    (hinj : ∀ e₁ ∈ F, ∀ e₂ ∈ F, G.ends e₁ = G.ends e₂ → e₁ = e₂) :
    (F.filter (fun e => ∀ a ∈ G.ends e, a ∈ S)).card ≤
      Nat.card ((sg G F).induce S).edgeSet := by
  classical
  rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  have h := induce_edges_eq G F S
  have h1 := congrArg Finset.card h
  rw [card_map] at h1
  rw [h1, card_image_of_injOn]
  · apply le_of_eq
    congr 1
    apply filter_congr
    intro e he
    simp [hl e he]
  · intro a ha b hb hab
    simp only [coe_filter, Set.mem_setOf_eq] at ha hb
    exact hinj a ha.1 b hb.1 hab

/-- Forests satisfy the subtour inequalities. -/
lemma forest_card_gamma (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (hF : G.IsForest F)
    (T : Finset V) (hT : T.Nonempty) :
    (F.filter (fun e => ∀ a ∈ G.ends e, a ∈ T)).card + 1 ≤ T.card := by
  classical
  have hl := forest_noLoop G F hF
  have hinj := forest_inj G F hF
  have hac := forest_acyclic G F hF
  have h1 := induce_card_ge G F (T : Set V) hl hinj
  have hac' := hac.induce (T : Set V)
  have : Nonempty (T : Set V) := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  have h2 := acyclic_card _ hac'
  have h3 : Fintype.card (T : Set V) = T.card := by simp
  simp only [Finset.mem_coe] at h1
  omega

lemma exists_mem_ends (G : CombOpt.HeldKarp.Graph V E) (e : E) : ∃ a, a ∈ G.ends e := by
  induction h : G.ends e using Sym2.ind with
  | h a b => exact ⟨a, Sym2.mem_mk_left a b⟩

/-- If every edge of `P` has its ends connected by `F`, then any point of the subtour
polytope puts total mass at most `|F|` on `P`. -/
lemma span_bound (G : CombOpt.HeldKarp.Graph V E) (F P : Finset E) (x : E → ℝ)
    (hx0 : ∀ e, 0 ≤ x e)
    (hxT : ∀ T : Finset V, T.Nonempty → ∑ e ∈ G.gamma T, x e ≤ (T.card : ℝ) - 1)
    (hspan : ∀ e ∈ P, ∀ a b, G.ends e = s(a, b) → (sg G F).Reachable a b) :
    ∑ e ∈ P, x e ≤ F.card := by
  classical
  set H := sg G F with hH
  let K : H.ConnectedComponent → Finset V :=
    fun c => univ.filter (fun v => H.connectedComponentMk v = c)
  have hgam : ∀ c e, e ∈ G.gamma (K c) ↔ ∀ a ∈ G.ends e, H.connectedComponentMk a = c := by
    intro c e
    simp [CombOpt.HeldKarp.Graph.gamma, K]
  -- every edge of `P` lies inside one component
  have hP : P ⊆ (univ : Finset H.ConnectedComponent).biUnion (fun c => G.gamma (K c)) := by
    intro e he
    rw [mem_biUnion]
    obtain ⟨a, ha⟩ := exists_mem_ends G e
    refine ⟨H.connectedComponentMk a, mem_univ _, ?_⟩
    rw [hgam]
    intro w hw
    induction h : G.ends e using Sym2.ind with
    | h p q =>
      rw [h] at ha hw
      have hr := hspan e he p q h
      rw [SimpleGraph.ConnectedComponent.eq]
      rcases Sym2.mem_iff.mp ha with rfl | rfl <;> rcases Sym2.mem_iff.mp hw with rfl | rfl
      · rfl
      · exact hr.symm
      · exact hr
      · rfl
  have hdisj : ∀ c ∈ (univ : Finset H.ConnectedComponent),
      ∀ c' ∈ (univ : Finset H.ConnectedComponent), c ≠ c' →
        Disjoint (G.gamma (K c)) (G.gamma (K c')) := by
    intro c _ c' _ hcc
    rw [disjoint_left]
    intro e h1 h2
    obtain ⟨a, ha⟩ := exists_mem_ends G e
    rw [hgam] at h1 h2
    exact hcc ((h1 a ha).symm.trans (h2 a ha))
  -- per-component bound
  have hcomp : ∀ c : H.ConnectedComponent,
      ((K c).card : ℝ) ≤ ((F.filter (fun e => ∀ a ∈ G.ends e, a ∈ K c)).card : ℝ) + 1 := by
    intro c
    have hconn := SimpleGraph.ConnectedComponent.connected_toSimpleGraph c
    have h1 := hconn.card_vert_le_card_edgeSet_add_one
    have h2 := induce_card_le G F c.supp
    have h3 : Nat.card c = (K c).card := by
      rw [← Nat.card_eq_finsetCard]
      apply Nat.card_congr
      exact Equiv.subtypeEquivRight (fun v => by
        rw [show (v ∈ c) ↔ H.connectedComponentMk v = c from Iff.rfl]; simp [K])
    replace h2 := h2.trans (card_le_card (t := F.filter (fun e => ∀ a ∈ G.ends e, a ∈ K c))
      (fun e he => by
        simp only [mem_filter] at he ⊢
        exact ⟨he.1, fun a ha => by simpa [K] using he.2 a ha⟩))
    have : Nat.card c ≤ (F.filter (fun e => ∀ a ∈ G.ends e, a ∈ K c)).card + 1 := by
      have h5 : Nat.card c.toSimpleGraph.edgeSet ≤
          (F.filter (fun e => ∀ a ∈ G.ends e, a ∈ K c)).card := h2
      omega
    rw [h3] at this
    exact_mod_cast this
  have hnonempty : ∀ c : H.ConnectedComponent, (K c).Nonempty := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨v, by simp [K]⟩
  calc ∑ e ∈ P, x e
      ≤ ∑ e ∈ (univ : Finset H.ConnectedComponent).biUnion (fun c => G.gamma (K c)), x e :=
        sum_le_sum_of_subset_of_nonneg hP (fun e _ _ => hx0 e)
    _ = ∑ c, ∑ e ∈ G.gamma (K c), x e := sum_biUnion hdisj
    _ ≤ ∑ c : H.ConnectedComponent, (((K c).card : ℝ) - 1) :=
        sum_le_sum (fun c _ => hxT (K c) (hnonempty c))
    _ ≤ ∑ c : H.ConnectedComponent,
          ((F.filter (fun e => ∀ a ∈ G.ends e, a ∈ K c)).card : ℝ) :=
        sum_le_sum (fun c _ => by linarith [hcomp c])
    _ = (((univ : Finset H.ConnectedComponent).biUnion
          (fun c => F.filter (fun e => ∀ a ∈ G.ends e, a ∈ K c))).card : ℝ) := by
        rw [card_biUnion]
        · push_cast; rfl
        · intro c _ c' _ hcc
          rw [Function.onFun, disjoint_left]
          intro e h1 h2
          obtain ⟨a, ha⟩ := exists_mem_ends G e
          have h1' := (mem_filter.mp h1).2 a ha
          have h2' := (mem_filter.mp h2).2 a ha
          simp only [K, mem_filter, mem_univ, true_and] at h1' h2'
          exact hcc (h1'.symm.trans h2')
    _ ≤ F.card := by
        exact_mod_cast card_le_card (biUnion_subset.mpr (fun c _ => filter_subset _ _))

/-! ### Abel summation -/

lemma abel_list {ι : Type*} (c a : ι → ℝ) : ∀ (l : List ι) (s M : ℝ),
    l.Pairwise (fun i j => c j ≤ c i) → (∀ i ∈ l, 0 ≤ c i ∧ c i ≤ M) → 0 ≤ M → s ≤ 0 →
    (∀ j, s + ((l.take j).map a).sum ≤ 0) →
    M * s + (l.map (fun i => c i * a i)).sum ≤ 0 := by
  intro l
  induction l with
  | nil =>
    intro s M _ _ hM hs _
    simp only [List.map_nil, List.sum_nil, add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos hM hs
  | cons i l ih =>
    intro s M hp hc hM hs hpre
    rw [List.pairwise_cons] at hp
    have hci := hc i (List.mem_cons_self)
    have hs' : s + a i ≤ 0 := by
      have := hpre 1; simpa using this
    have h := ih (s + a i) (c i) hp.2
      (fun j hj => ⟨(hc j (List.mem_cons_of_mem i hj)).1, hp.1 j hj⟩) hci.1 hs'
      (fun j => by
        have := hpre (j + 1)
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at this
        linarith)
    simp only [List.map_cons, List.sum_cons]
    have h2 : (M - c i) * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith [hci.2]) hs
    nlinarith

/-! ### The greedy forest -/

def reachE (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (e : E) : Prop :=
  ∃ a b, G.ends e = s(a, b) ∧ (sg G F).Reachable a b

noncomputable def step (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (e : E) : Finset E :=
  if ¬ (G.ends e).IsDiag ∧ ¬ reachE G F e then insert e F else F

noncomputable def greedy (G : CombOpt.HeldKarp.Graph V E) (l : List E) : Finset E :=
  l.foldl (step G) ∅

def Inv (G : CombOpt.HeldKarp.Graph V E) (l : List E) (F : Finset E) : Prop :=
  F ⊆ l.toFinset ∧ (∀ e ∈ F, ¬ (G.ends e).IsDiag) ∧
  (∀ e₁ ∈ F, ∀ e₂ ∈ F, G.ends e₁ = G.ends e₂ → e₁ = e₂) ∧ (sg G F).IsAcyclic ∧
  (∀ e ∈ l, ∀ a b, G.ends e = s(a, b) → (sg G F).Reachable a b)

lemma sg_insert (G : CombOpt.HeldKarp.Graph V E) (F : Finset E) (e : E) (a b : V)
    (he : G.ends e = s(a, b)) : sg G (insert e F) = sg G F ⊔ SimpleGraph.edge a b := by
  ext u v
  rw [SimpleGraph.sup_adj, sg_adj, sg_adj, SimpleGraph.edge_adj]
  constructor
  · rintro ⟨⟨e', he', hee⟩, hne⟩
    rw [mem_insert] at he'
    rcases he' with rfl | he'
    · right
      refine ⟨?_, hne⟩
      have := he.symm.trans hee
      rcases Sym2.eq_iff.mp this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
    · left; exact ⟨⟨e', he', hee⟩, hne⟩
  · rintro (⟨⟨e', he', hee⟩, hne⟩ | ⟨hab, hne⟩)
    · exact ⟨⟨e', mem_insert_of_mem he', hee⟩, hne⟩
    · refine ⟨⟨e, mem_insert_self e F, ?_⟩, hne⟩
      rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact he
      · rw [he, Sym2.eq_swap]

lemma inv_step (G : CombOpt.HeldKarp.Graph V E) (l : List E) (F : Finset E) (e : E)
    (h : Inv G l F) : Inv G (l ++ [e]) (step G F e) := by
  classical
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold step
  split_ifs with hc
  · obtain ⟨hnl, hnr⟩ := hc
    induction hab : G.ends e using Sym2.ind with
    | h a b =>
    have hne : a ≠ b := by rw [hab, Sym2.mk_isDiag_iff] at hnl; exact hnl
    have hnreach : ¬ (sg G F).Reachable a b := fun hr => hnr ⟨a, b, hab, hr⟩
    have hsg := sg_insert G F e a b hab
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro e' he'
      rw [mem_insert] at he'
      rw [List.mem_toFinset, List.mem_append]
      rcases he' with rfl | he'
      · right; simp
      · left; exact List.mem_toFinset.mp (h1 he')
    · intro e' he'
      rw [mem_insert] at he'
      rcases he' with rfl | he'
      · exact hnl
      · exact h2 e' he'
    · have key : ∀ e' ∈ F, G.ends e' ≠ G.ends e := by
        intro e' he' heq
        apply hnreach
        apply SimpleGraph.Adj.reachable
        rw [sg_adj]
        exact ⟨⟨e', he', heq.trans hab⟩, hne⟩
      intro e₁ he₁ e₂ he₂ heq
      rw [mem_insert] at he₁ he₂
      rcases he₁ with rfl | he₁ <;> rcases he₂ with rfl | he₂
      · rfl
      · exact absurd heq.symm (key e₂ he₂)
      · exact absurd heq (key e₁ he₁)
      · exact h3 e₁ he₁ e₂ he₂ heq
    · rw [hsg]; exact h4.sup_edge_of_not_reachable hnreach
    · intro e' he' u v huv
      rw [List.mem_append] at he'
      rcases he' with he' | he'
      · exact (h5 e' he' u v huv).mono (sg_mono G (subset_insert e F))
      · rw [List.mem_singleton] at he'
        subst he'
        rw [hab] at huv
        have hadj : (sg G (insert e' F)).Adj a b := by
          rw [sg_adj]; exact ⟨⟨e', mem_insert_self _ _, hab⟩, hne⟩
        rcases Sym2.eq_iff.mp huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hadj.reachable
        · exact hadj.reachable.symm
  · refine ⟨fun e' he' => ?_, h2, h3, h4, ?_⟩
    · rw [List.toFinset_append]; exact mem_union_left _ (h1 he')
    · intro e' he' u v huv
      rw [List.mem_append] at he'
      rcases he' with he' | he'
      · exact h5 e' he' u v huv
      · rw [List.mem_singleton] at he'
        subst he'
        rw [not_and_or, not_not, not_not] at hc
        rcases hc with hd | ⟨a, b, hab, hr⟩
        · rw [huv, Sym2.mk_isDiag_iff] at hd
          subst hd; rfl
        · rw [huv] at hab
          rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hr
          · exact hr.symm

lemma inv_foldl (G : CombOpt.HeldKarp.Graph V E) : ∀ (l l₀ : List E) (F₀ : Finset E),
    Inv G l₀ F₀ → Inv G (l₀ ++ l) (l.foldl (step G) F₀) := by
  intro l
  induction l with
  | nil => intro l₀ F₀ h; simpa using h
  | cons e l ih =>
    intro l₀ F₀ h
    rw [List.foldl_cons]
    have := ih (l₀ ++ [e]) (step G F₀ e) (inv_step G l₀ F₀ e h)
    simpa using this

lemma inv_greedy (G : CombOpt.HeldKarp.Graph V E) (l : List E) : Inv G l (greedy G l) := by
  have h0 : Inv G [] ∅ := by
    refine ⟨empty_subset _, by simp, by simp, ?_, by simp⟩
    intro v c hc
    cases c with
    | nil => exact SimpleGraph.Walk.IsCycle.not_of_nil hc
    | cons h _ =>
      rw [sg_adj] at h
      obtain ⟨⟨e, he, _⟩, _⟩ := h
      simp at he
  show Inv G l (l.foldl (step G) ∅)
  simpa using inv_foldl G l [] ∅ h0

lemma foldl_bounds (G : CombOpt.HeldKarp.Graph V E) : ∀ (l : List E) (F₀ : Finset E),
    F₀ ⊆ l.foldl (step G) F₀ ∧ l.foldl (step G) F₀ ⊆ F₀ ∪ l.toFinset := by
  intro l
  induction l with
  | nil => intro F₀; simp
  | cons e l ih =>
    intro F₀
    rw [List.foldl_cons]
    obtain ⟨ih1, ih2⟩ := ih (step G F₀ e)
    have hs1 : F₀ ⊆ step G F₀ e := by
      unfold step; split_ifs
      · exact subset_insert _ _
      · exact le_rfl
    have hs2 : step G F₀ e ⊆ insert e F₀ := by
      unfold step; split_ifs
      · exact le_rfl
      · exact subset_insert _ _
    refine ⟨hs1.trans ih1, ih2.trans ?_⟩
    intro x hx
    rw [mem_union] at hx ⊢
    rcases hx with hx | hx
    · have := hs2 hx
      rw [mem_insert] at this
      rcases this with rfl | h
      · right; simp
      · left; exact h
    · right; rw [List.toFinset_cons]; exact mem_insert_of_mem hx

lemma greedy_prefix (G : CombOpt.HeldKarp.Graph V E) (l₁ l₂ : List E)
    (hnd : (l₁ ++ l₂).Nodup) :
    greedy G (l₁ ++ l₂) ∩ l₁.toFinset = greedy G l₁ := by
  classical
  unfold greedy
  rw [List.foldl_append]
  obtain ⟨hb1, hb2⟩ := foldl_bounds G l₂ (l₁.foldl (step G) ∅)
  have hsub : l₁.foldl (step G) ∅ ⊆ l₁.toFinset := (inv_greedy G l₁).1
  apply subset_antisymm
  · intro x hx
    rw [mem_inter] at hx
    have := hb2 hx.1
    rw [mem_union] at this
    rcases this with h | h
    · exact h
    · exfalso
      rw [List.nodup_append] at hnd
      exact hnd.2.2 x (List.mem_toFinset.mp hx.2) x (List.mem_toFinset.mp h) rfl
  · intro x hx
    exact mem_inter.mpr ⟨hb1 hx, hsub hx⟩

/-- The greedy forest dominates every point of the subtour polytope for the weights `c`. -/
lemma greedy_opt (G : CombOpt.HeldKarp.Graph V E) (c x : E → ℝ) (hx0 : ∀ e, 0 ≤ x e)
    (hxT : ∀ T : Finset V, T.Nonempty → ∑ e ∈ G.gamma T, x e ≤ (T.card : ℝ) - 1) :
    ∃ F : Finset E, G.IsForest F ∧ ∑ e, c e * x e ≤ ∑ e ∈ F, c e := by
  classical
  set A := univ.filter (fun e => 0 < c e) with hA
  let r : E → E → Prop := fun i j => c j ≤ c i
  haveI : Std.Total r := ⟨fun i j => le_total (c j) (c i)⟩
  haveI : IsTrans E r := ⟨fun i j k hij hjk => le_trans hjk hij⟩
  set l := A.toList.insertionSort r with hl
  have hsorted : l.Pairwise r := List.pairwise_insertionSort r _
  have hperm := List.perm_insertionSort r A.toList
  have hnd : l.Nodup := hperm.nodup_iff.mpr (nodup_toList A)
  have hlA : l.toFinset = A := by
    ext e; rw [List.mem_toFinset, hperm.mem_iff, mem_toList]
  set F := greedy G l with hF
  obtain ⟨i1, i2, i3, i4, i5⟩ := inv_greedy G l
  refine ⟨F, isForest_of G F i2 i3 i4, ?_⟩
  let a : E → ℝ := fun e => x e - if e ∈ F then 1 else 0
  have hpre : ∀ j, 0 + ((l.take j).map a).sum ≤ 0 := by
    intro j
    have hsplit : l = l.take j ++ l.drop j := (List.take_append_drop j l).symm
    have hnd1 : (l.take j).Nodup := hnd.sublist (List.take_sublist j l)
    rw [zero_add, ← List.sum_toFinset _ hnd1]
    have hpref := greedy_prefix G (l.take j) (l.drop j) (by rw [← hsplit]; exact hnd)
    rw [← hsplit] at hpref
    have hsp := span_bound G (greedy G (l.take j)) (l.take j).toFinset x hx0 hxT
      (fun e he u v huv => (inv_greedy G (l.take j)).2.2.2.2 e (List.mem_toFinset.mp he) u v huv)
    simp only [a, sum_sub_distrib, sum_boole]
    have : ((l.take j).toFinset.filter (fun e => e ∈ F)) = greedy G (l.take j) := by
      rw [← hpref]; ext e; simp [hF, and_comm]
    rw [this]
    linarith
  set M := ∑ e ∈ A, c e
  have hcA : ∀ i ∈ l, 0 ≤ c i ∧ c i ≤ M := by
    intro i hi
    have hiA : i ∈ A := by rw [← hlA]; exact List.mem_toFinset.mpr hi
    refine ⟨(mem_filter.mp hiA).2.le, ?_⟩
    exact single_le_sum (f := c) (fun e he => (mem_filter.mp he).2.le) hiA
  have hM : 0 ≤ M := sum_nonneg (fun e he => (mem_filter.mp he).2.le)
  have habel := abel_list c a l 0 M hsorted hcA hM le_rfl hpre
  rw [mul_zero, zero_add, ← List.sum_toFinset _ hnd, hlA] at habel
  have hFA : F ⊆ A := by rw [← hlA]; exact i1
  have h1 : ∑ e ∈ A, c e * a e = ∑ e ∈ A, c e * x e - ∑ e ∈ F, c e := by
    simp only [a, mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, inter_eq_right.mpr hFA]
  have h2 : ∑ e, c e * x e ≤ ∑ e ∈ A, c e * x e := by
    rw [← sum_filter_add_sum_filter_not univ (fun e => 0 < c e)]
    have : ∑ e ∈ univ.filter (fun e => ¬ 0 < c e), c e * x e ≤ 0 := by
      apply sum_nonpos
      intro e he
      rw [mem_filter, not_lt] at he
      exact mul_nonpos_of_nonpos_of_nonneg he.2 (hx0 e)
    rw [hA]; linarith
  linarith

end ForestPolyAux

open ForestPolyAux in
theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    (G : CombOpt.HeldKarp.Graph V E) :
    convexHull ℝ {x : E → ℝ | ∃ F : Finset E, G.IsForest F ∧ x = fun e => if e ∈ F then 1 else 0} =
      {x : E → ℝ | (∀ T : Finset V, T.Nonempty → ∑ e ∈ G.gamma T, x e ≤ (T.card : ℝ) - 1) ∧
        ∀ e : E, 0 ≤ x e} := by
  classical
  set X := {x : E → ℝ | ∃ F : Finset E, G.IsForest F ∧ x = fun e => if e ∈ F then 1 else 0}
    with hX
  set P := {x : E → ℝ | (∀ T : Finset V, T.Nonempty → ∑ e ∈ G.gamma T, x e ≤ (T.card : ℝ) - 1) ∧
        ∀ e : E, 0 ≤ x e} with hP
  have hgam : ∀ (T : Finset V) (F : Finset E),
      (∑ e ∈ G.gamma T, (if e ∈ F then (1 : ℝ) else 0)) =
        ((F.filter (fun e => ∀ a ∈ G.ends e, a ∈ T)).card : ℝ) := by
    intro T F
    rw [sum_boole]
    congr 1
    congr 1
    ext e
    simp [CombOpt.HeldKarp.Graph.gamma, and_comm]
  have hXP : X ⊆ P := by
    rintro x ⟨F, hF, rfl⟩
    refine ⟨fun T hT => ?_, fun e => by simp only; split_ifs <;> norm_num⟩
    rw [hgam]
    have := forest_card_gamma G F hF T hT
    have h' : ((F.filter (fun e => ∀ a ∈ G.ends e, a ∈ T)).card : ℝ) + 1 ≤ T.card := by
      exact_mod_cast this
    linarith
  have hPconv : Convex ℝ P := by
    intro x hx y hy a b ha hb hab
    refine ⟨fun T hT => ?_, fun e => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum]
      have h1 := hx.1 T hT
      have h2 := hy.1 T hT
      have := add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
      rw [← add_mul, hab, one_mul] at this
      linarith
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (hx.2 e)) (mul_nonneg hb (hy.2 e))
  apply subset_antisymm
  · exact convexHull_min hXP hPconv
  · intro x hx
    by_contra hnot
    have hfin : X.Finite := by
      apply (Set.finite_range (fun F : Finset E => fun e => if e ∈ F then (1 : ℝ) else 0)).subset
      rintro y ⟨F, _, rfl⟩
      exact ⟨F, rfl⟩
    have hclosed : IsClosed (convexHull ℝ X) := (Set.Finite.isCompact_convexHull (𝕜 := ℝ) hfin).isClosed
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ X)
      hclosed hnot
    let c : E → ℝ := fun e => f (Pi.single e 1)
    have hf : ∀ y : E → ℝ, f y = ∑ e, c e * y e := by
      intro y
      conv_lhs => rw [← Finset.univ_sum_single y]
      rw [map_sum]
      apply sum_congr rfl
      intro e _
      have : (Pi.single e (y e) : E → ℝ) = y e • (Pi.single e 1 : E → ℝ) := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this, map_smul, smul_eq_mul]
      ring
    obtain ⟨F, hF, hFc⟩ := greedy_opt G c x hx.2 hx.1
    have hmem : (fun e => if e ∈ F then (1 : ℝ) else 0) ∈ convexHull ℝ X :=
      subset_convexHull ℝ X ⟨F, hF, rfl⟩
    have h1 := hfu _ hmem
    rw [hf] at h1 hux
    have h2 : ∑ e, c e * (if e ∈ F then (1 : ℝ) else 0) = ∑ e ∈ F, c e := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [sum_ite_mem, univ_inter]
    rw [h2] at h1
    linarith
