-- Prove2me | solution 1 for FordFulkerson56.Planar.ab_planar_exists_topmost_chain_walk
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T06:48:58.026251+00:00
-- url     : https://prove2.me/submissions/f23de28c-2073-45a0-ae4b-55cc76cba088

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.TakeDrop
import Definitions.Def_FordFulkerson56_MinCut_Network
import Definitions.Def_FordFulkerson56_MinCut_IsChain
import Definitions.Def_FordFulkerson56_Planar_ABPlaneDrawing
import Definitions.Def_Schoenflies_FaceCyclesLand
import Definitions.Def_Schoenflies_Graph_Redrawing
import Definitions.Def_Schoenflies_Subarc

open FordFulkerson56.MinCut
open FordFulkerson56.Planar
open Set Schoenflies unitInterval
open scoped Graph

namespace SolFordFulkerson56Topmost

set_option linter.unusedSectionVars false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-! ### Section 1: Embedding `ℝ × ℝ` into `Schoenflies.Plane` and building the plane graph -/

private noncomputable def toPlane (p : ℝ × ℝ) : Plane :=
  Plane.mk p.1 p.2

private theorem toPlane_injective : Function.Injective toPlane := by
  intro p q h
  have h0 : toPlane p 0 = toPlane q 0 := congrArg (fun x : Plane => x 0) h
  have h1 : toPlane p 1 = toPlane q 1 := congrArg (fun x : Plane => x 1) h
  simp only [toPlane, Plane.mk_zero, Plane.mk_one] at h0 h1
  exact Prod.ext h0 h1

private theorem toPlane_eq_linear (p : ℝ × ℝ) :
    toPlane p = p.1 • Plane.mk 1 0 + p.2 • Plane.mk 0 1 := by
  ext i
  fin_cases i <;> simp [toPlane]

private theorem continuous_toPlane : Continuous toPlane := by
  have h : toPlane = fun p : ℝ × ℝ => p.1 • Plane.mk 1 0 + p.2 • Plane.mk 0 1 := by
    ext p i
    rw [toPlane_eq_linear]
  rw [h]
  fun_prop

private noncomputable def vPt {N : Network V E} (D₀ : ABPlaneDrawing N) (v : V) : Plane :=
  toPlane (D₀.vertex v)

private theorem vPt_injective {N : Network V E} (D₀ : ABPlaneDrawing N) :
    Function.Injective (vPt D₀) :=
  toPlane_injective.comp D₀.vertex_injective

@[simp]
private theorem vPt_inj {N : Network V E} (D₀ : ABPlaneDrawing N) {u v : V} :
    vPt D₀ u = vPt D₀ v ↔ u = v :=
  (vPt_injective D₀).eq_iff

private noncomputable def abGraph (N : Network V E) (D₀ : ABPlaneDrawing N) :
    Graph Plane (Option E) where
  vertexSet := Set.range (vPt D₀)
  IsLink e x y :=
    (x = vPt D₀ (endA N e) ∧ y = vPt D₀ (endB N e)) ∨
    (x = vPt D₀ (endB N e) ∧ y = vPt D₀ (endA N e))
  edgeSet := Set.univ
  isLink_symm := fun _ _ => ⟨fun _ _ h => by tauto⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w hxy hvw
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun _ => ⟨vPt D₀ (endA N e), vPt D₀ (endB N e), Or.inl ⟨rfl, rfl⟩⟩, fun _ => trivial⟩
  left_mem_of_isLink := by
    rintro e x y (⟨rfl, -⟩ | ⟨rfl, -⟩)
    exacts [⟨endA N e, rfl⟩, ⟨endB N e, rfl⟩]

@[simp]
private theorem abGraph_vertexSet (N : Network V E) (D₀ : ABPlaneDrawing N) :
    V(abGraph N D₀) = Set.range (vPt D₀) := rfl

@[simp]
private theorem abGraph_edgeSet (N : Network V E) (D₀ : ABPlaneDrawing N) :
    E(abGraph N D₀) = Set.univ := rfl

@[simp]
private theorem abGraph_isLink (N : Network V E) (D₀ : ABPlaneDrawing N)
    {e : Option E} {x y : Plane} :
    (abGraph N D₀).IsLink e x y ↔
      (x = vPt D₀ (endA N e) ∧ y = vPt D₀ (endB N e)) ∨
      (x = vPt D₀ (endB N e) ∧ y = vPt D₀ (endA N e)) := Iff.rfl

private instance abGraph_finite (N : Network V E) (D₀ : ABPlaneDrawing N) :
    Graph.Finite (abGraph N D₀) where
  finite_vertexSet := (Set.finite_range (vPt D₀)).to_subtype
  finite_edgeSet := Set.toFinite _

private noncomputable def rawDrawing {N : Network V E} (D₀ : ABPlaneDrawing N)
    (e : Option E) (t : ℝ) : Plane :=
  toPlane (D₀.arc e (Set.projIcc (0 : ℝ) 1 zero_le_one t))

private theorem rawDrawing_zero {N : Network V E} (D₀ : ABPlaneDrawing N) (e : Option E) :
    rawDrawing D₀ e 0 = vPt D₀ (endA N e) := by
  simp [rawDrawing, vPt]

private theorem rawDrawing_one {N : Network V E} (D₀ : ABPlaneDrawing N) (e : Option E) :
    rawDrawing D₀ e 1 = vPt D₀ (endB N e) := by
  simp [rawDrawing, vPt]

private theorem isDrawing_rawDrawing {N : Network V E} (D₀ : ABPlaneDrawing N) :
    Graph.IsDrawing (abGraph N D₀) (rawDrawing D₀) where
  edge_param := by
    intro e _
    refine ⟨?_, ?_, ?_⟩
    · have hc : Continuous (rawDrawing D₀ e) :=
        continuous_toPlane.comp ((D₀.arc e).continuous.comp continuous_projIcc)
      exact hc.continuousOn
    · intro s hs t ht hst
      have hproj : Set.projIcc (0 : ℝ) 1 zero_le_one s = Set.projIcc (0 : ℝ) 1 zero_le_one t :=
        D₀.arc_injective e (toPlane_injective hst)
      have hs' : (Set.projIcc (0 : ℝ) 1 zero_le_one s : ℝ) = s :=
        congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hs)
      have ht' : (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ) = t :=
        congrArg Subtype.val (Set.projIcc_of_mem zero_le_one ht)
      rw [← hs', ← ht', hproj]
    · rw [rawDrawing_zero, rawDrawing_one]
      exact Or.inl ⟨rfl, rfl⟩
  vertex_mem_edgeArc := by
    rintro e x y v hl ⟨w, rfl⟩ ⟨t, ht, htv⟩
    have harc : D₀.arc e (Set.projIcc (0 : ℝ) 1 zero_le_one t) = D₀.vertex w :=
      toPlane_injective htv
    have hw := D₀.arc_avoids_vertices e _ w harc
    rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hw with rfl | rfl <;> simp
  edge_inter := by
    rintro e f _ _ hef p ⟨s, hs, rfl⟩ ⟨t, ht, hst⟩
    have harc : D₀.arc e (Set.projIcc (0 : ℝ) 1 zero_le_one s) =
        D₀.arc f (Set.projIcc (0 : ℝ) 1 zero_le_one t) :=
      toPlane_injective hst.symm
    obtain ⟨hs01, ht01⟩ := D₀.arcs_meet_only_at_ends e f hef _ _ harc
    have hpe : rawDrawing D₀ e s = vPt D₀ (endA N e) ∨ rawDrawing D₀ e s = vPt D₀ (endB N e) := by
      rcases hs01 with hs0 | hs1
      · left; simp [rawDrawing, vPt, hs0]
      · right; simp [rawDrawing, vPt, hs1]
    have hpf : rawDrawing D₀ f t = vPt D₀ (endA N f) ∨ rawDrawing D₀ f t = vPt D₀ (endB N f) := by
      rcases ht01 with ht0 | ht1
      · left; simp [rawDrawing, vPt, ht0]
      · right; simp [rawDrawing, vPt, ht1]
    refine ⟨?_, ?_, ?_⟩
    · rcases hpe with h | h <;> exact h ▸ ⟨_, rfl⟩
    · rcases hpe with h | h
      · exact h ▸ ⟨vPt D₀ (endB N e), Or.inl ⟨rfl, rfl⟩⟩
      · exact h ▸ ⟨vPt D₀ (endA N e), Or.inr ⟨rfl, rfl⟩⟩
    · rw [← hst]
      rcases hpf with h | h
      · exact h ▸ ⟨vPt D₀ (endB N f), Or.inl ⟨rfl, rfl⟩⟩
      · exact h ▸ ⟨vPt D₀ (endA N f), Or.inr ⟨rfl, rfl⟩⟩

/-! ### Section 2: Bijection between `IsChainWalk` and `Graph.IsPath` avoiding `none` -/

private def Step (N : Network V E) (e : E) (u v : V) : Prop :=
  (u = N.tail e ∧ v = N.head e) ∨ (u = N.head e ∧ v = N.tail e)

private theorem isLink_some_iff {N : Network V E} {D₀ : ABPlaneDrawing N}
    {e : E} {u v : V} :
    (abGraph N D₀).IsLink (some e) (vPt D₀ u) (vPt D₀ v) ↔ Step N e u v := by
  simp [abGraph, Step, endA, endB]

private theorem step_endpoints_cases {N : Network V E} {e : E} {x₁ y₁ x₂ y₂ : V}
    (h1 : Step N e x₁ y₁) (h2 : Step N e x₂ y₂) :
    (x₁ = x₂ ∧ y₁ = y₂) ∨ (x₁ = y₂ ∧ y₁ = x₂) := by
  rcases h1 with ⟨hx1, hy1⟩ | ⟨hx1, hy1⟩ <;> rcases h2 with ⟨hx2, hy2⟩ | ⟨hx2, hy2⟩
  · exact Or.inl ⟨hx1.trans hx2.symm, hy1.trans hy2.symm⟩
  · exact Or.inr ⟨hx1.trans hy2.symm, hy1.trans hx2.symm⟩
  · exact Or.inr ⟨hx1.trans hy2.symm, hy1.trans hx2.symm⟩
  · exact Or.inl ⟨hx1.trans hx2.symm, hy1.trans hy2.symm⟩

private theorem chainWalk_head_eq {N : Network V E} {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) :
    ∃ (h0 : 0 < vs.length), vs[0]'h0 = u := by
  have h0 : 0 < vs.length := by have := hw.1; omega
  refine ⟨h0, ?_⟩
  have hhead := hw.2.1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0] at hhead
  exact Option.some.inj hhead

private theorem chainWalk_last_eq {N : Network V E} {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) :
    ∃ (hl : p.length < vs.length), vs[p.length]'hl = w := by
  have hl : p.length < vs.length := by have := hw.1; omega
  refine ⟨hl, ?_⟩
  have hlast := hw.2.2.1
  rw [List.getLast?_eq_getElem?] at hlast
  have hidx : vs.length - 1 = p.length := by have := hw.1; omega
  rw [hidx, List.getElem?_eq_getElem hl] at hlast
  exact Option.some.inj hlast

private theorem chainWalk_step_at {N : Network V E} {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) (i : ℕ) (hi : i < p.length) :
    Step N (p[i]'hi) (vs[i]'(by have := hw.1; omega)) (vs[i + 1]'(by have := hw.1; omega)) := by
  have hi_vs : i < vs.length := by have := hw.1; omega
  have hi1_vs : i + 1 < vs.length := by have := hw.1; omega
  have hstep := hw.2.2.2.2.2 i hi
  rw [List.getElem?_eq_getElem hi_vs, List.getElem?_eq_getElem hi1_vs] at hstep
  rcases hstep with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨Option.some.inj h1, Option.some.inj h2⟩
  · exact Or.inr ⟨Option.some.inj h1, Option.some.inj h2⟩

private theorem isChainWalk_drop {N : Network V E} {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) (k : ℕ) (hk : k < vs.length) :
    IsChainWalk N (vs[k]'hk) w (p.drop k) (vs.drop k) := by
  have hlen : (vs.drop k).length = (p.drop k).length + 1 := by
    simp only [List.length_drop]; have := hw.1; omega
  refine ⟨hlen, ?_, ?_, hw.2.2.2.1.sublist (List.drop_sublist _ _),
    hw.2.2.2.2.1.sublist (List.drop_sublist _ _), ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero, List.getElem?_eq_getElem hk]
  · obtain ⟨hl, hlast_eq⟩ := chainWalk_last_eq hw
    rw [List.getLast?_eq_getElem?]
    have hidx : (vs.drop k).length - 1 = p.length - k := by
      simp only [List.length_drop]; have := hw.1; omega
    have hk_p : k + (p.length - k) = p.length := by have := hw.1; omega
    rw [hidx, List.getElem?_drop, hk_p, List.getElem?_eq_getElem hl, hlast_eq]
  · intro i hi
    simp only [List.length_drop] at hi
    have hki : k + i < p.length := by omega
    have hstep := hw.2.2.2.2.2 (k + i) hki
    rw [List.getElem?_drop, List.getElem?_drop]
    simpa [Nat.add_assoc, List.getElem_drop] using hstep

private theorem isChainWalk_cons {N : Network V E} {u v w : V} {e₀ : E} {p : List E} {vs : List V}
    (hw : IsChainWalk N v w p vs) (he₀ : Step N e₀ u v) (hu : u ∉ vs) :
    IsChainWalk N u w (e₀ :: p) (u :: vs) := by
  have hlen : (u :: vs).length = (e₀ :: p).length + 1 := by simp [hw.1]
  have he₀_not_mem : e₀ ∉ p := by
    intro hmem
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
    have hstep_i := chainWalk_step_at hw i hi
    rcases step_endpoints_cases he₀ hstep_i with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hu (List.getElem_mem _)
    · exact hu (List.getElem_mem _)
  refine ⟨hlen, rfl, ?_, List.nodup_cons.mpr ⟨hu, hw.2.2.2.1⟩,
    List.nodup_cons.mpr ⟨he₀_not_mem, hw.2.2.2.2.1⟩, ?_⟩
  · cases vs with
    | nil => have := hw.1; simp at this
    | cons x xs => simpa using hw.2.2.1
  · intro i hi
    cases i with
    | zero =>
      obtain ⟨h0, hv0⟩ := chainWalk_head_eq hw
      have h1 : (u :: vs)[1]? = some v := by simp [List.getElem?_eq_getElem h0, hv0]
      rcases he₀ with ⟨hu_eq, hv_eq⟩ | ⟨hu_eq, hv_eq⟩
      · exact Or.inl ⟨by simp [hu_eq], by simpa [hv_eq] using h1⟩
      · exact Or.inr ⟨by simp [hu_eq], by simpa [hv_eq] using h1⟩
    | succ j =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      simpa using hw.2.2.2.2.2 j hi

private theorem isPath_of_isChainWalk {N : Network V E} (D₀ : ABPlaneDrawing N) :
    ∀ {p : List E} {u w : V} {vs : List V},
      IsChainWalk N u w p vs →
      (abGraph N D₀).IsPath (vPt D₀ u) (p.map Option.some) (vPt D₀ w) ∧
        (abGraph N D₀).walkVertices (vPt D₀ u) (p.map Option.some) =
          vPt D₀ '' {v | v ∈ vs}
  | [], u, w, vs, hw => by
    obtain ⟨h0, hu0⟩ := chainWalk_head_eq hw
    obtain ⟨hl, hwl⟩ := chainWalk_last_eq hw
    have huw : u = w := by simpa [hu0] using hwl
    subst huw
    have hvs : vs = [u] := by
      cases vs with
      | nil => simp at h0
      | cons x xs =>
        cases xs with
        | nil =>
          simp only [List.getElem_cons_zero] at hu0
          rw [hu0]
        | cons y ys =>
          have := hw.1
          simp at this
    subst hvs
    refine ⟨Graph.IsPath.nil ⟨u, rfl⟩, ?_⟩
    ext z
    simp [Graph.walkVertices]
  | e₀ :: p', u, w, vs, hw => by
    obtain ⟨h0, hu0⟩ := chainWalk_head_eq hw
    have h1 : 1 < vs.length := by have := hw.1; simp at this; omega
    have hstep0 : Step N e₀ u (vs[1]'h1) := by
      have hs := chainWalk_step_at hw 0 (by simp)
      simpa [hu0] using hs
    have hw_tail : IsChainWalk N (vs[1]'h1) w p' (vs.drop 1) := by
      simpa using isChainWalk_drop hw 1 h1
    obtain ⟨hpath_tail, hverts_tail⟩ := isPath_of_isChainWalk D₀ hw_tail
    have hvs_eq : vs = u :: vs.drop 1 := by
      cases vs with
      | nil => simp at h0
      | cons x xs =>
        simp only [List.getElem_cons_zero] at hu0
        simp [hu0]
    have hu_not_mem : u ∉ vs.drop 1 := by
      have hnodup := hw.2.2.2.1
      rw [hvs_eq, List.nodup_cons] at hnodup
      exact hnodup.1
    have hfresh : vPt D₀ u ∉ (abGraph N D₀).walkVertices (vPt D₀ (vs[1]'h1)) (p'.map Option.some) := by
      rw [hverts_tail]
      rintro ⟨v, hv, hveq⟩
      exact hu_not_mem ((vPt_injective D₀ hveq) ▸ hv)
    have hlink : (abGraph N D₀).IsLink (some e₀) (vPt D₀ u) (vPt D₀ (vs[1]'h1)) :=
      isLink_some_iff.mpr hstep0
    have hpath : (abGraph N D₀).IsPath (vPt D₀ u) (some e₀ :: p'.map Option.some) (vPt D₀ w) :=
      Graph.IsPath.cons hlink hpath_tail hfresh
    refine ⟨hpath, ?_⟩
    ext z
    constructor
    · intro hz
      rcases Graph.mem_walkVertices_cons hlink hz with rfl | hz'
      · exact ⟨u, by rw [hvs_eq]; exact List.mem_cons_self, rfl⟩
      · rw [hverts_tail] at hz'
        rcases hz' with ⟨v, hv, rfl⟩
        exact ⟨v, by rw [hvs_eq]; exact List.mem_cons_of_mem _ hv, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      rw [Set.mem_setOf_eq, hvs_eq] at hv
      rcases List.mem_cons.mp hv with rfl | hv'
      · exact Graph.mem_walkVertices_self
      · refine Graph.mem_walkVertices_cons_of_mem hlink ?_
        rw [hverts_tail]
        exact ⟨v, hv', rfl⟩

private theorem exists_isChainWalk_of_isPath {N : Network V E} (D₀ : ABPlaneDrawing N)
    {x y : Plane} {W : List (Option E)}
    (hP : (abGraph N D₀).IsPath x W y) (hnone : none ∉ W) :
    ∃ (u w : V) (p : List E) (vs : List V),
      x = vPt D₀ u ∧ y = vPt D₀ w ∧ W = p.map Option.some ∧
      IsChainWalk N u w p vs ∧
      (abGraph N D₀).walkVertices x W = vPt D₀ '' {v | v ∈ vs} := by
  induction hP with
  | @nil x hx =>
    rcases hx with ⟨u, rfl⟩
    refine ⟨u, u, [], [u], rfl, rfl, rfl, ?_, ?_⟩
    · refine ⟨rfl, rfl, rfl, List.nodup_singleton u, List.nodup_nil, ?_⟩
      intro i hi; simp at hi
    · ext z; simp [Graph.walkVertices]
  | @cons x z y oe W' hl hW' hfresh ih =>
    have hoe : oe ≠ none := fun h => hnone (h ▸ List.mem_cons_self)
    obtain ⟨e₀, rfl⟩ := Option.ne_none_iff_exists'.mp hoe
    have hnone' : none ∉ W' := fun h => hnone (List.mem_cons_of_mem _ h)
    obtain ⟨v, w, p', vs', rfl, rfl, rfl, hw', hverts'⟩ := ih hnone'
    rcases hl.left_mem with ⟨u, hxu⟩
    have hstep : Step N e₀ u v := by
      rw [← hxu] at hl
      exact isLink_some_iff.mp hl
    have hu_not_vs' : u ∉ vs' := by
      intro hu
      apply hfresh
      rw [← hxu, hverts']
      exact ⟨u, hu, rfl⟩
    refine ⟨u, w, e₀ :: p', u :: vs', hxu.symm, rfl, rfl, isChainWalk_cons hw' hstep hu_not_vs', ?_⟩
    subst hxu
    ext q
    constructor
    · intro hq
      rcases Graph.mem_walkVertices_cons hl hq with rfl | hq'
      · exact ⟨u, List.mem_cons_self, rfl⟩
      · rw [hverts'] at hq'
        rcases hq' with ⟨v', hv', rfl⟩
        exact ⟨v', List.mem_cons_of_mem _ hv', rfl⟩
    · rintro ⟨v', hv', rfl⟩
      rcases List.mem_cons.mp hv' with rfl | hv'
      · exact Graph.mem_walkVertices_self
      · refine Graph.mem_walkVertices_cons_of_mem hl ?_
        rw [hverts']
        exact ⟨v', hv', rfl⟩

/-! ### Section 3: Ear extraction and ear rerouting on `Graph.IsPath` -/

private theorem suffix_from_set {α β : Type*} {G : Graph α β} {u v : α} {W : List β}
    {S₁ : Set α} (hP : G.IsPath u W v) (hS₁ : ∃ z ∈ G.walkVertices u W, z ∈ S₁) :
    ∃ x ∈ S₁, ∃ T ⊆ W,
      G.IsPath x T v ∧
      x ∈ G.walkVertices u W ∧
      G.walkVertices x T ⊆ G.walkVertices u W ∧
      ∀ z ∈ G.walkVertices x T, z ≠ x → z ∉ S₁ := by
  induction hP with
  | @nil u hu =>
    rcases hS₁ with ⟨z, hz, hzS⟩
    rw [Graph.walkVertices_nil, Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨z, hzS, [], List.Subset.refl _, Graph.IsPath.nil hu, Graph.mem_walkVertices_self,
      Set.Subset.refl _, ?_⟩
    intro q hq hne
    rw [Graph.walkVertices_nil, Set.mem_singleton_iff] at hq
    exact absurd hq hne
  | @cons u w v e W' hl hW' hfresh ih =>
    by_cases hw : ∃ z ∈ G.walkVertices w W', z ∈ S₁
    · obtain ⟨x, hxS, T, hTW', hT, hxW', hsub, havoid⟩ := ih hw
      refine ⟨x, hxS, T, List.Subset.trans hTW' (List.subset_cons_self _ _), hT,
        Graph.mem_walkVertices_cons_of_mem hl hxW',
        fun z hz => Graph.mem_walkVertices_cons_of_mem hl (hsub hz), havoid⟩
    · rcases hS₁ with ⟨z, hz, hzS⟩
      rcases Graph.mem_walkVertices_cons hl hz with rfl | hz'
      · refine ⟨z, hzS, e :: W', List.Subset.refl _, Graph.IsPath.cons hl hW' hfresh,
          Graph.mem_walkVertices_self, Set.Subset.refl _, ?_⟩
        intro q hq hne hqS
        rcases Graph.mem_walkVertices_cons hl hq with rfl | hq'
        · exact hne rfl
        · exact hw ⟨q, hq', hqS⟩
      · exact absurd ⟨z, hz', hzS⟩ hw

private theorem prefix_to_set {α β : Type*} {G : Graph α β} {u v : α} {W : List β}
    {S₂ : Set α} (hP : G.IsPath u W v) (hv : v ∈ S₂) :
    ∃ y ∈ S₂, ∃ K ⊆ W,
      G.IsPath u K y ∧
      y ∈ G.walkVertices u W ∧
      G.walkVertices u K ⊆ G.walkVertices u W ∧
      ∀ z ∈ G.walkVertices u K, z ≠ y → z ∉ S₂ := by
  induction hP with
  | @nil u hu =>
    refine ⟨u, hv, [], List.Subset.refl _, Graph.IsPath.nil hu, Graph.mem_walkVertices_self,
      Set.Subset.refl _, ?_⟩
    intro z hz hne
    rw [Graph.walkVertices_nil, Set.mem_singleton_iff] at hz
    exact absurd hz hne
  | @cons u w v e W' hl hW' hfresh ih =>
    by_cases huS : u ∈ S₂
    · refine ⟨u, huS, [], List.nil_subset _, Graph.IsPath.nil hl.left_mem,
        Graph.mem_walkVertices_self, ?_, ?_⟩
      · intro z hz
        rw [Graph.walkVertices_nil, Set.mem_singleton_iff] at hz
        exact hz ▸ Graph.mem_walkVertices_self
      · intro z hz hne
        rw [Graph.walkVertices_nil, Set.mem_singleton_iff] at hz
        exact absurd hz hne
    · obtain ⟨y, hyS, K', hK'W', hK', hyW', hsub, havoid⟩ := ih hv
      have hfreshK : u ∉ G.walkVertices w K' := fun h => hfresh (hsub h)
      refine ⟨y, hyS, e :: K', List.cons_subset_cons _ hK'W',
        Graph.IsPath.cons hl hK' hfreshK,
        Graph.mem_walkVertices_cons_of_mem hl hyW', ?_, ?_⟩
      · intro z hz
        rcases Graph.mem_walkVertices_cons hl hz with rfl | hz'
        · exact Graph.mem_walkVertices_self
        · exact Graph.mem_walkVertices_cons_of_mem hl (hsub hz')
      · intro z hz hzy
        rcases Graph.mem_walkVertices_cons hl hz with rfl | hz'
        · exact huS
        · exact havoid z hz' hzy

private theorem extract_ear {α β : Type*} {G : Graph α β} {u v : α} {W : List β}
    {V_D S₁ S₂ : Set α}
    (hP : G.IsPath u W v) (hu : u ∈ S₁) (hv : v ∈ S₂) (hdisj : Disjoint S₁ S₂)
    (hpart : ∀ z ∈ G.walkVertices u W, z ∈ V_D → z ∈ S₁ ∨ z ∈ S₂) :
    ∃ x ∈ S₁, ∃ y ∈ S₂, ∃ K ⊆ W,
      x ≠ y ∧
      G.IsPath x K y ∧
      G.walkVertices x K ⊆ G.walkVertices u W ∧
      ∀ z ∈ G.walkVertices x K, z ≠ x → z ≠ y → z ∉ V_D := by
  obtain ⟨x, hxS₁, T, hTW, hT, hxW, hTsub, hTavoid⟩ :=
    suffix_from_set hP ⟨u, Graph.mem_walkVertices_self, hu⟩
  obtain ⟨y, hyS₂, K, hKT, hK, hyT, hKsub, hKavoid⟩ := prefix_to_set hT hv
  have hxy : x ≠ y := fun h => Set.disjoint_left.mp hdisj hxS₁ (h ▸ hyS₂)
  refine ⟨x, hxS₁, y, hyS₂, K, List.Subset.trans hKT hTW, hxy, hK,
    Set.Subset.trans hKsub hTsub, ?_⟩
  intro z hz hzx hzy hzD
  have hzW : z ∈ G.walkVertices u W := hTsub (hKsub hz)
  rcases hpart z hzW hzD with hz1 | hz2
  · exact hTavoid z (hKsub hz) hzx hz1
  · exact hKavoid z hz hzy hz2

private theorem reroute_ear_aux {α β : Type*} {G : Graph α β} {a b x y : α}
    {P Q₁ Q₂ K : List β}
    (hP : G.IsPath a P x) (hQ1 : G.IsPath x Q₁ y) (hQ2 : G.IsPath y Q₂ b)
    (hK : G.IsPath x K y) (hxy : x ≠ y)
    (hM1 : ∀ z ∈ G.walkVertices a P, z ∈ G.walkVertices x (Q₁ ++ Q₂) → z = x)
    (hM2 : ∀ z ∈ G.walkVertices x Q₁, z ∈ G.walkVertices y Q₂ → z = y)
    (hint : ∀ z ∈ G.walkVertices x K, z ≠ x → z ≠ y →
      z ∉ G.walkVertices a (P ++ (Q₁ ++ Q₂))) :
    G.IsPath a (P ++ (K ++ Q₂)) b := by
  have hQ2_sub_Q : G.walkVertices y Q₂ ⊆ G.walkVertices x (Q₁ ++ Q₂) := by
    intro z hz
    rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
    · exact Graph.walkVertices_mono (List.subset_append_left _ _) hQ1.target_mem_walkVertices
    · exact Graph.mem_walkVertices_of_mem_covered
        (Graph.coveredVertices_mono (List.subset_append_right _ _) hcov)
  have hQ_sub_D : G.walkVertices x (Q₁ ++ Q₂) ⊆ G.walkVertices a (P ++ (Q₁ ++ Q₂)) := by
    intro z hz
    rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
    · exact Graph.walkVertices_mono (List.subset_append_left _ _) hP.target_mem_walkVertices
    · exact Graph.mem_walkVertices_of_mem_covered
        (Graph.coveredVertices_mono (List.subset_append_right _ _) hcov)
  have hP_sub_D : G.walkVertices a P ⊆ G.walkVertices a (P ++ (Q₁ ++ Q₂)) :=
    Graph.walkVertices_mono (List.subset_append_left _ _)
  have hKQ2 : G.IsPath x (K ++ Q₂) b := by
    refine hK.append hQ2 fun z hzK hzQ2 => ?_
    by_contra hzy
    have hzx : z = x := by
      by_contra hzx
      exact hint z hzK hzx hzy (hQ_sub_D (hQ2_sub_Q hzQ2))
    subst hzx
    exact hxy (hM2 z Graph.mem_walkVertices_self hzQ2)
  refine hP.append hKQ2 fun z hzP hzKQ2 => ?_
  have hz_cases : z ∈ G.walkVertices x K ∨ z ∈ G.walkVertices y Q₂ := by
    rcases Graph.mem_walkVertices_iff.mp hzKQ2 with rfl | hcov
    · exact Or.inl Graph.mem_walkVertices_self
    rw [Graph.coveredVertices_append] at hcov
    rcases hcov with hcovK | hcovQ2
    · exact Or.inl (Graph.mem_walkVertices_of_mem_covered hcovK)
    · exact Or.inr (Graph.mem_walkVertices_of_mem_covered hcovQ2)
  rcases hz_cases with hzK | hzQ2
  · by_contra hzx
    have hzy : z = y := by
      by_contra hzy
      exact hint z hzK hzx hzy (hP_sub_D hzP)
    subst hzy
    exact hxy.symm (hM1 z hzP (hQ2_sub_Q Graph.mem_walkVertices_self))
  · exact hM1 z hzP (hQ2_sub_Q hzQ2)

private theorem exists_rerouted_path {α β : Type*} {G : Graph α β} {a b x y : α}
    {D K : List β}
    (hD : G.IsPath a D b) (hK : G.IsPath x K y) (hxy : x ≠ y)
    (hx : x ∈ G.walkVertices a D) (hy : y ∈ G.walkVertices a D)
    (hint : ∀ z ∈ G.walkVertices x K, z ≠ x → z ≠ y → z ∉ G.walkVertices a D) :
    ∃ D' : List β,
      G.IsPath a D' b ∧
      (∀ g ∈ K, g ∈ D') ∧
      (∀ g ∈ D', g ∈ D ∨ g ∈ K) := by
  obtain ⟨P, Q, hPQ, hP, hQ, hM1⟩ := hD.split_meet hx
  have hy_cases : y ∈ G.walkVertices x Q ∨ y ∈ G.walkVertices a P := by
    rw [hPQ] at hy
    rcases Graph.mem_walkVertices_iff.mp hy with rfl | hcov
    · exact Or.inr Graph.mem_walkVertices_self
    rw [Graph.coveredVertices_append] at hcov
    rcases hcov with h | h
    · exact Or.inr (Graph.mem_walkVertices_of_mem_covered h)
    · exact Or.inl (Graph.mem_walkVertices_of_mem_covered h)
  rcases hy_cases with hyQ | hyP
  · obtain ⟨Q₁, Q₂, hQ12, hQ1, hQ2, hM2⟩ := hQ.split_meet hyQ
    have hD_eq : D = P ++ (Q₁ ++ Q₂) := by rw [hPQ, hQ12]
    have hpath' : G.IsPath a (P ++ (K ++ Q₂)) b :=
      reroute_ear_aux hP hQ1 hQ2 hK hxy (hQ12 ▸ hM1) hM2 (hD_eq ▸ hint)
    refine ⟨P ++ (K ++ Q₂), hpath', ?_, ?_⟩
    · intro g hg
      exact List.mem_append_right _ (List.mem_append_left _ hg)
    · intro g hg
      rcases List.mem_append.mp hg with hgP | hgKQ2
      · exact Or.inl (hD_eq ▸ List.mem_append_left _ hgP)
      · rcases List.mem_append.mp hgKQ2 with hgK | hgQ2
        · exact Or.inr hgK
        · exact Or.inl (hD_eq ▸ List.mem_append_right _ (List.mem_append_right _ hgQ2))
  · obtain ⟨P₁, P₂, hP12, hP1, hP2, hM2⟩ := hP.split_meet hyP
    have hP1sub : G.walkVertices a P₁ ⊆ G.walkVertices a P :=
      Graph.walkVertices_mono (hP12 ▸ List.subset_append_left _ _)
    have hP2sub : G.walkVertices y P₂ ⊆ G.walkVertices a P := by
      intro z hz
      rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
      · exact hyP
      · exact Graph.mem_walkVertices_of_mem_covered
          (Graph.coveredVertices_mono (hP12 ▸ List.subset_append_right _ _) hcov)
    have hM1' : ∀ z ∈ G.walkVertices a P₁, z ∈ G.walkVertices y (P₂ ++ Q) → z = y := by
      intro z hz hz'
      rcases Graph.mem_walkVertices_iff.mp hz' with rfl | hcov
      · rfl
      rw [Graph.coveredVertices_append] at hcov
      rcases hcov with h | h
      · exact hM2 z hz (Graph.mem_walkVertices_of_mem_covered h)
      · exfalso
        obtain rfl : z = x := hM1 z (hP1sub hz) (Graph.mem_walkVertices_of_mem_covered h)
        exact hxy (hM2 z hz hP2.target_mem_walkVertices)
    have hM2' : ∀ z ∈ G.walkVertices y P₂, z ∈ G.walkVertices x Q → z = x :=
      fun z hz hz' => hM1 z (hP2sub hz) hz'
    have hD_eq : D = P₁ ++ (P₂ ++ Q) := by rw [hPQ, hP12, List.append_assoc]
    have hKrev_verts : G.walkVertices y K.reverse = G.walkVertices x K :=
      hK.isWalk.walkVertices_reverse_eq (hK.ne_nil hxy)
    have hint_rev : ∀ z ∈ G.walkVertices y K.reverse, z ≠ y → z ≠ x →
        z ∉ G.walkVertices a (P₁ ++ (P₂ ++ Q)) := by
      intro z hz hzy hzx
      rw [hKrev_verts] at hz
      rw [← hD_eq]
      exact hint z hz hzx hzy
    have hpath' : G.IsPath a (P₁ ++ (K.reverse ++ Q)) b :=
      reroute_ear_aux hP1 hP2 hQ hK.reverse hxy.symm hM1' hM2' hint_rev
    refine ⟨P₁ ++ (K.reverse ++ Q), hpath', ?_, ?_⟩
    · intro g hg
      exact List.mem_append_right _ (List.mem_append_left _ (List.mem_reverse.mpr hg))
    · intro g hg
      rcases List.mem_append.mp hg with hgP1 | hgKQ
      · exact Or.inl (hD_eq ▸ List.mem_append_left _ hgP1)
      · rcases List.mem_append.mp hgKQ with hgK | hgQ
        · exact Or.inr (List.mem_reverse.mp hgK)
        · exact Or.inl (hD_eq ▸ List.mem_append_right _ (List.mem_append_right _ hgQ))

/-! ### Section 4: Extremal choice of `D` minimizing edges inside `J(D)` -/

private noncomputable def insideEdges (drawing : Option E → ℝ → Plane)
    (D : List (Option E)) : Finset (Option E) := by
  classical
  exact Finset.univ.filter fun e : Option E =>
    (Graph.edgeArc drawing e ∩ Schoenflies.inside (Graph.edgesCover drawing (none :: D))).Nonempty

private noncomputable def insideScore (drawing : Option E → ℝ → Plane)
    (D : List (Option E)) : ℕ :=
  (insideEdges drawing D).card

private theorem ear_inter_cycle_eq {β : Type*} {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {e : β} {a b x y : Plane} {D K : List β}
    (h : Graph.IsDrawing G drawing) (hc : G.IsCycleThrough e a b D)
    (hK : G.IsPath x K y) (hxy : x ≠ y)
    (hx : x ∈ G.walkVertices a D) (hy : y ∈ G.walkVertices a D)
    (hint : ∀ z ∈ G.walkVertices x K, z ≠ x → z ≠ y → z ∉ G.walkVertices a D)
    (hnew : ∀ g ∈ K, g ∉ e :: D) :
    Graph.edgesCover drawing K ∩ Graph.edgesCover drawing (e :: D) = {x, y} := by
  have hKarc : IsArcBetween (Graph.edgesCover drawing K) x y :=
    h.path_isArcBetween hK (hK.ne_nil hxy)
  have hB₀ := hc.cycleGraph_le
  have hxJ : x ∈ Graph.edgesCover drawing (e :: D) := by
    rw [← h.pointSet_cycleGraph hc]
    exact Graph.vertexSet_subset_pointSet (hc.cycleGraph_vertexSet ▸ hx)
  have hyJ : y ∈ Graph.edgesCover drawing (e :: D) := by
    rw [← h.pointSet_cycleGraph hc]
    exact Graph.vertexSet_subset_pointSet (hc.cycleGraph_vertexSet ▸ hy)
  refine Set.Subset.antisymm ?_ ?_
  · rintro z ⟨hzK, hzJ⟩
    obtain ⟨g₁, hg₁, hzg₁⟩ := Graph.mem_edgesCover_iff.mp hzK
    obtain ⟨g₂, hg₂, hzg₂⟩ := Graph.mem_edgesCover_iff.mp hzJ
    have hne : g₁ ≠ g₂ := fun hEq => hnew g₁ hg₁ (hEq ▸ hg₂)
    have hg₂E : g₂ ∈ E(G) := by
      rcases List.mem_cons.mp hg₂ with rfl | hg₂'
      exacts [hc.isLink.edge_mem, hc.isPath.edge_mem hg₂']
    obtain ⟨hzV, hinc₁, -⟩ := h.edge_inter (hK.edge_mem hg₁) hg₂E hne hzg₁ hzg₂
    have hzW_K : z ∈ G.walkVertices x K :=
      Graph.mem_walkVertices_of_mem_covered ⟨g₁, hg₁, hinc₁⟩
    have hzW_D : z ∈ G.walkVertices a D :=
      h.mem_walkVertices_of_mem_edgesCover hc hzV hzJ
    by_contra hcon
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hcon
    exact hint z hzW_K hcon.1 hcon.2 hzW_D
  · rintro z (rfl | rfl)
    exacts [⟨hKarc.left_mem, hxJ⟩, ⟨hKarc.right_mem, hyJ⟩]

private theorem ear_subset_outside_of_minimal {N : Network V E} {D₀ : ABPlaneDrawing N}
    {drawing : Option E → ℝ → Plane}
    (h : Graph.IsDrawing (abGraph N D₀) drawing)
    (hpoly : ∀ g ∈ E(abGraph N D₀), IsPolygonal (Graph.edgeArc drawing g))
    {D : List (Option E)}
    (hD : (abGraph N D₀).IsPath (vPt D₀ N.source) D (vPt D₀ N.sink))
    (hnone : none ∉ D)
    (hmin : ∀ D', (abGraph N D₀).IsPath (vPt D₀ N.source) D' (vPt D₀ N.sink) →
      none ∉ D' → insideScore drawing D ≤ insideScore drawing D')
    {x y : Plane} {K : List (Option E)}
    (hK : (abGraph N D₀).IsPath x K y) (hxy : x ≠ y)
    (hx : x ∈ (abGraph N D₀).walkVertices (vPt D₀ N.source) D)
    (hy : y ∈ (abGraph N D₀).walkVertices (vPt D₀ N.source) D)
    (hint : ∀ z ∈ (abGraph N D₀).walkVertices x K, z ≠ x → z ≠ y →
      z ∉ (abGraph N D₀).walkVertices (vPt D₀ N.source) D)
    (hnew : ∀ g ∈ K, g ∉ none :: D) :
    Graph.edgesCover drawing K \ {x, y} ⊆
      Schoenflies.outside (Graph.edgesCover drawing (none :: D)) := by
  set G := abGraph N D₀
  set aPt := vPt D₀ N.source
  set bPt := vPt D₀ N.sink
  set J := Graph.edgesCover drawing (none :: D)
  have hlink_none : G.IsLink none aPt bPt := Or.inl ⟨rfl, rfl⟩
  have hc : G.IsCycleThrough none aPt bPt D := ⟨hlink_none, hD, hnone⟩
  have hsep : IsSeparating J := h.cycle_isSeparating hpoly hc
  have hKarc : IsArcBetween (Graph.edgesCover drawing K) x y :=
    h.path_isArcBetween hK (hK.ne_nil hxy)
  have hinter : Graph.edgesCover drawing K ∩ J = {x, y} :=
    ear_inter_cycle_eq h hc hK hxy hx hy hint hnew
  have hdisjJ : Disjoint (Graph.edgesCover drawing K \ {x, y}) J := by
    rw [Set.disjoint_left]
    intro z hz hzJ
    exact hz.2 (hinter ▸ ⟨hz.1, hzJ⟩)
  obtain ⟨W, V_reg, hpair, hsubW⟩ :=
    hsep.exists_isRegionPair_subset hKarc.isPreconnected_diff hKarc.nonempty_diff hdisjJ
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- Suppose for contradiction `edgesCover drawing K \ {x, y} ⊆ inside J`.
    exfalso
    obtain ⟨D', hD', hKD', hD'sub⟩ := exists_rerouted_path hD hK hxy hx hy hint
    have hnone_K : none ∉ K := fun hn => hnew none hn List.mem_cons_self
    have hnone' : none ∉ D' := by
      intro hn
      rcases hD'sub none hn with h1 | h2
      exacts [hnone h1, hnone_K h2]
    have hc' : G.IsCycleThrough none aPt bPt D' := ⟨hlink_none, hD', hnone'⟩
    set J' := Graph.edgesCover drawing (none :: D')
    have hsep' : IsSeparating J' := h.cycle_isSeparating hpoly hc'
    have hKJ' : Graph.edgesCover drawing K ⊆ J' :=
      Graph.edgesCover_mono fun g hg => List.mem_cons_of_mem _ (hKD' g hg)
    have hJ'sub : J' ⊆ J ∪ Schoenflies.inside J := by
      intro z hz
      obtain ⟨g, hg, hzg⟩ := Graph.mem_edgesCover_iff.mp hz
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact Or.inl (Graph.mem_edgesCover List.mem_cons_self hzg)
      · rcases hD'sub g hg' with hgD | hgK
        · exact Or.inl (Graph.mem_edgesCover (List.mem_cons_of_mem _ hgD) hzg)
        · have hzK : z ∈ Graph.edgesCover drawing K := Graph.mem_edgesCover hgK hzg
          by_cases hzxy : z ∈ ({x, y} : Set Plane)
          · exact Or.inl ((hinter ▸ hzxy).2)
          · exact Or.inr (hsubW ⟨hzK, hzxy⟩)
    have hout_disj : Disjoint (Schoenflies.outside J) J' := by
      rw [Set.disjoint_left]
      intro z hzout hzJ'
      rcases hJ'sub hzJ' with hzJ | hzin
      · exact hzout.1 hzJ
      · exact Set.disjoint_left.mp disjoint_inside_outside hzin hzout
    have hout_sub : Schoenflies.outside J ⊆ Schoenflies.outside J' := by
      obtain ⟨W', V', hpair', hsub'⟩ :=
        hsep'.exists_isRegionPair_subset hsep.isConnected_outside.isPreconnected
          hsep.isConnected_outside.nonempty hout_disj
      rcases hpair' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd (hsep'.isBounded_inside.subset hsub') hsep.not_isBounded_outside
      · exact hsub'
    have hin_sub : Schoenflies.inside J' ⊆ Schoenflies.inside J \ Graph.edgesCover drawing K :=
      cell_subset_region_diff hsep hsep' (Or.inl ⟨rfl, rfl⟩) (Or.inr ⟨rfl, rfl⟩) hout_sub hKJ'
    obtain ⟨z₀, hz₀⟩ := hKarc.nonempty_diff
    obtain ⟨e₀, he₀K, hz₀e₀⟩ := Graph.mem_edgesCover_iff.mp hz₀.1
    have hz₀_in : z₀ ∈ Schoenflies.inside J := hsubW hz₀
    have hcard_lt : insideScore drawing D' < insideScore drawing D := by
      classical
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro e he
        simp only [insideEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
        rcases he with ⟨w, hw1, hw2⟩
        exact ⟨w, hw1, (hin_sub hw2).1⟩
      · intro hEq
        have he₀_in : e₀ ∈ insideEdges drawing D := by
          simp only [insideEdges, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨z₀, hz₀e₀, hz₀_in⟩
        have he₀_in' : e₀ ∈ insideEdges drawing D' := hEq ▸ he₀_in
        simp only [insideEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he₀_in'
        rcases he₀_in' with ⟨w, hwe₀, hwin'⟩
        exact (hin_sub hwin').2 (Graph.mem_edgesCover he₀K hwe₀)
    exact Nat.lt_irrefl _ (lt_of_lt_of_le hcard_lt (hmin D' hD' hnone'))
  · exact hsubW

/-! ### Section 5: Alternating crosscuts in `outside J` must intersect -/

private theorem closure_isRegionOf_subset {K W : Set Plane}
    (hK : IsClosed K) (hreg : IsRegionOf K W) :
    closure W ⊆ W ∪ K := by
  intro q hq_cl
  by_cases hqK : q ∈ K
  · exact Or.inr hqK
  · left
    have hq_compl : q ∈ Kᶜ := hqK
    have hUopen : IsOpen (connectedComponentIn Kᶜ q) :=
      Plane.isOpen_connectedComponentIn hK.isOpen_compl
    have hqU : q ∈ connectedComponentIn Kᶜ q := mem_connectedComponentIn hq_compl
    obtain ⟨w, hwU, hwW⟩ := Metric.mem_closure_iff.mp hq_cl
      |> fun _ => mem_closure_iff.mp hq_cl (connectedComponentIn Kᶜ q) hUopen hqU
    have hcomp_eq : connectedComponentIn Kᶜ q = connectedComponentIn Kᶜ w :=
      connectedComponentIn_eq hwU
    rcases hreg with rfl | rfl
    · exact connectedComponentIn_subset_inside hwW (hcomp_eq ▸ hqU)
    · exact connectedComponentIn_subset_outside hwW (hcomp_eq ▸ hqU)

private theorem alternating_crosscuts_outside_inter {J A₁ A₂ P₁ P₂ : Set Plane}
    {x₁ y₁ x₂ y₂ : Plane}
    (hJsep : IsSeparating J) (hJpoly : IsPolygonal J) (hP₁poly : IsPolygonal P₁)
    (hA₁ : IsArcBetween A₁ x₁ y₁) (hA₂ : IsArcBetween A₂ x₁ y₁)
    (hunion : A₁ ∪ A₂ = J) (hinter : A₁ ∩ A₂ = {x₁, y₁})
    (hP₁ : IsArcBetween P₁ x₁ y₁) (hP₁J : P₁ ∩ J = {x₁, y₁})
    (hP₁out : P₁ \ {x₁, y₁} ⊆ Schoenflies.outside J)
    (hP₂ : IsArcBetween P₂ x₂ y₂)
    (hP₂out : P₂ \ {x₂, y₂} ⊆ Schoenflies.outside J)
    (hx₂ : x₂ ∈ A₂ \ {x₁, y₁}) (hy₂ : y₂ ∈ A₁ \ {x₁, y₁}) :
    (P₁ ∩ P₂).Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  obtain ⟨z₂, hz₂⟩ := hP₂.nonempty_diff
  have hz₂_diff : z₂ ∈ Schoenflies.outside J \ P₁ :=
    ⟨hP₂out hz₂, fun hzP₁ => Set.eq_empty_iff_forall_notMem.mp hempty z₂ ⟨hzP₁, hz₂.1⟩⟩
  have hQsub : P₂ \ {x₂, y₂} ⊆ Schoenflies.outside J \ P₁ :=
    fun z hz => ⟨hP₂out hz, fun hzP₁ => Set.eq_empty_iff_forall_notMem.mp hempty z ⟨hzP₁, hz.1⟩⟩
  have hQcomp : P₂ \ {x₂, y₂} ⊆ connectedComponentIn (Schoenflies.outside J \ P₁) z₂ :=
    hP₂.isPreconnected_diff.subset_connectedComponentIn hz₂ hQsub
  have hx₂_cl : x₂ ∈ closure (connectedComponentIn (Schoenflies.outside J \ P₁) z₂) :=
    closure_mono hQcomp hP₂.left_mem_closure_diff
  have hy₂_cl : y₂ ∈ closure (connectedComponentIn (Schoenflies.outside J \ P₁) z₂) :=
    closure_mono hQcomp hP₂.right_mem_closure_diff
  have hsplit := Schoenflies.crosscutSplitsRegion J A₁ A₂ P₁ (Schoenflies.outside J) x₁ y₁
    hJsep hJpoly hP₁poly hA₁ hA₂ hunion hinter hP₁ hP₁J (IsRegionOf.outside J) hP₁out z₂ hz₂_diff
  set W := connectedComponentIn (Schoenflies.outside J \ P₁) z₂
  have hWJ : Disjoint W J := by
    rw [Set.disjoint_left]
    intro z hzW hzJ
    exact (connectedComponentIn_subset _ _ hzW).1.1 hzJ
  rcases hsplit with hreg₁ | hreg₂
  · have hclosed₁ : IsClosed (A₁ ∪ P₁) :=
      (hA₁.isArc.isCompact.union hP₁.isArc.isCompact).isClosed
    have hx₂_mem := closure_isRegionOf_subset hclosed₁ hreg₁ hx₂_cl
    have hx₂J : x₂ ∈ J := hunion ▸ Or.inr hx₂.1
    rcases hx₂_mem with hx₂W | (hx₂A₁ | hx₂P₁)
    · exact Set.disjoint_left.mp hWJ hx₂W hx₂J
    · exact hx₂.2 (hinter ▸ ⟨hx₂A₁, hx₂.1⟩)
    · exact hx₂.2 (hP₁J ▸ ⟨hx₂P₁, hx₂J⟩)
  · have hclosed₂ : IsClosed (A₂ ∪ P₁) :=
      (hA₂.isArc.isCompact.union hP₁.isArc.isCompact).isClosed
    have hy₂_mem := closure_isRegionOf_subset hclosed₂ hreg₂ hy₂_cl
    have hy₂J : y₂ ∈ J := hunion ▸ Or.inl hy₂.1
    rcases hy₂_mem with hy₂W | (hy₂A₂ | hy₂P₁)
    · exact Set.disjoint_left.mp hWJ hy₂W hy₂J
    · exact hy₂.2 (hinter ▸ ⟨hy₂.1, hy₂A₂⟩)
    · exact hy₂.2 (hP₁J ▸ ⟨hy₂P₁, hy₂J⟩)

private theorem ear_edges_notMem_of_split {α β : Type*} {G : Graph α β}
    {u₁ u₂ u₃ x y : α} {L₁ L₂ K : List β}
    (_hL₁ : G.IsPath u₁ L₁ u₂) (_hL₂ : G.IsPath u₂ L₂ u₃)
    (hK : G.IsPath x K y)
    (hx_not_L₂ : x ∉ G.walkVertices u₂ L₂)
    (hy_not_L₁ : y ∉ G.walkVertices u₁ L₁)
    (hint : ∀ z ∈ G.walkVertices x K, z ≠ x → z ≠ y →
      z ∉ G.walkVertices u₁ L₁ ∪ G.walkVertices u₂ L₂) :
    ∀ g ∈ K, g ∉ L₁ ++ L₂ := by
  intro g hgK hgL
  obtain ⟨p, q, hl⟩ := G.exists_isLink_of_mem_edgeSet (hK.edge_mem hgK)
  have hpq : p ≠ q := fun h => hK.not_isLoopAt hgK p (h ▸ hl)
  have hpK : p ∈ G.walkVertices x K :=
    Graph.mem_walkVertices_of_mem_covered ⟨g, hgK, hl.inc_left⟩
  have hqK : q ∈ G.walkVertices x K :=
    Graph.mem_walkVertices_of_mem_covered ⟨g, hgK, hl.inc_right⟩
  rcases List.mem_append.mp hgL with hgL₁ | hgL₂
  · have hpL₁ : p ∈ G.walkVertices u₁ L₁ :=
      Graph.mem_walkVertices_of_mem_covered ⟨g, hgL₁, hl.inc_left⟩
    have hqL₁ : q ∈ G.walkVertices u₁ L₁ :=
      Graph.mem_walkVertices_of_mem_covered ⟨g, hgL₁, hl.inc_right⟩
    have hp_xy : p = x ∨ p = y := by
      by_contra hcon
      rw [not_or] at hcon
      exact hint p hpK hcon.1 hcon.2 (Or.inl hpL₁)
    have hq_xy : q = x ∨ q = y := by
      by_contra hcon
      rw [not_or] at hcon
      exact hint q hqK hcon.1 hcon.2 (Or.inl hqL₁)
    rcases hp_xy with rfl | rfl <;> rcases hq_xy with rfl | rfl
    · exact hpq rfl
    · exact hy_not_L₁ hqL₁
    · exact hy_not_L₁ hpL₁
    · exact hpq rfl
  · have hpL₂ : p ∈ G.walkVertices u₂ L₂ :=
      Graph.mem_walkVertices_of_mem_covered ⟨g, hgL₂, hl.inc_left⟩
    have hqL₂ : q ∈ G.walkVertices u₂ L₂ :=
      Graph.mem_walkVertices_of_mem_covered ⟨g, hgL₂, hl.inc_right⟩
    have hp_xy : p = x ∨ p = y := by
      by_contra hcon
      rw [not_or] at hcon
      exact hint p hpK hcon.1 hcon.2 (Or.inr hpL₂)
    have hq_xy : q = x ∨ q = y := by
      by_contra hcon
      rw [not_or] at hcon
      exact hint q hqK hcon.1 hcon.2 (Or.inr hqL₂)
    rcases hp_xy with rfl | rfl <;> rcases hq_xy with rfl | rfl
    · exact hpq rfl
    · exact hx_not_L₂ hpL₂
    · exact hx_not_L₂ hqL₂
    · exact hpq rfl

private theorem isChainWalk_take {N : Network V E} {u w : V} {p : List E} {vs : List V}
    (hw : IsChainWalk N u w p vs) (k : ℕ) (hk : k < vs.length) :
    IsChainWalk N u (vs[k]'hk) (p.take k) (vs.take (k + 1)) := by
  have hk_p : k ≤ p.length := by have := hw.1; omega
  have hlen : (vs.take (k + 1)).length = (p.take k).length + 1 := by
    simp only [List.length_take]; have := hw.1; omega
  refine ⟨hlen, ?_, ?_, hw.2.2.2.1.sublist (List.take_sublist _ _),
    hw.2.2.2.2.1.sublist (List.take_sublist _ _), ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_take_of_lt (by omega),
      ← List.head?_eq_getElem?, hw.2.1]
  · rw [List.getLast?_eq_getElem?]
    have hidx : (vs.take (k + 1)).length - 1 = k := by
      simp only [List.length_take]; omega
    rw [hidx, List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hk]
  · intro i hi
    simp only [List.length_take, lt_min_iff] at hi
    have hstep := hw.2.2.2.2.2 i hi.2
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_take_of_lt (by omega)]
    simpa [List.getElem_take] using hstep

private theorem edgesCover_inter_walkVertices_nonempty {β : Type*}
    {G : Graph Plane β} {drawing : β → ℝ → Plane}
    {x₁ y₁ x₂ y₂ : Plane} {K₁ K₂ : List β}
    (h : Graph.IsDrawing G drawing)
    (hK₁ : G.IsPath x₁ K₁ y₁) (hK₂ : G.IsPath x₂ K₂ y₂)
    (hinter : (Graph.edgesCover drawing K₁ ∩ Graph.edgesCover drawing K₂).Nonempty) :
    (G.walkVertices x₁ K₁ ∩ G.walkVertices x₂ K₂).Nonempty := by
  rcases hinter with ⟨z, hz₁, hz₂⟩
  obtain ⟨g₁, hg₁, hzg₁⟩ := Graph.mem_edgesCover_iff.mp hz₁
  obtain ⟨g₂, hg₂, hzg₂⟩ := Graph.mem_edgesCover_iff.mp hz₂
  by_cases hEq : g₁ = g₂
  · subst hEq
    obtain ⟨p, q, hl⟩ := G.exists_isLink_of_mem_edgeSet (hK₁.edge_mem hg₁)
    exact ⟨p,
      Graph.mem_walkVertices_of_mem_covered ⟨g₁, hg₁, hl.inc_left⟩,
      Graph.mem_walkVertices_of_mem_covered ⟨g₁, hg₂, hl.inc_left⟩⟩
  · obtain ⟨-, hinc₁, hinc₂⟩ :=
      h.edge_inter (hK₁.edge_mem hg₁) (hK₂.edge_mem hg₂) hEq hzg₁ hzg₂
    exact ⟨z,
      Graph.mem_walkVertices_of_mem_covered ⟨g₁, hg₁, hinc₁⟩,
      Graph.mem_walkVertices_of_mem_covered ⟨g₂, hg₂, hinc₂⟩⟩

end SolFordFulkerson56Topmost

open FordFulkerson56.MinCut
open FordFulkerson56.Planar
open Set Schoenflies unitInterval
open scoped Graph
open SolFordFulkerson56Topmost

theorem solution {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (N : FordFulkerson56.MinCut.Network V E)
    (_hno_ab : ∀ e : E, ¬ ((N.tail e = N.source ∧ N.head e = N.sink) ∨
      (N.tail e = N.sink ∧ N.head e = N.source)))
    (hconn : ∃ C : Finset E, FordFulkerson56.MinCut.IsChain N N.source N.sink C)
    (hplanar : Nonempty (ABPlaneDrawing N)) :
    ∃ (p : List E) (vs : List V),
      FordFulkerson56.MinCut.IsChainWalk N N.source N.sink p vs ∧
      ∀ (j₁ j₂ : ℕ) (_hj₁ : 0 < j₁) (hj₁₂ : j₁ < j₂) (hj₂ : j₂ + 1 < vs.length)
        (p₁ p₂ : List E) (vs₁ vs₂ : List V),
        FordFulkerson56.MinCut.IsChainWalk N (vs[j₁]'(by omega)) N.sink p₁ vs₁ →
        FordFulkerson56.MinCut.IsChainWalk N N.source (vs[j₂]'(by omega)) p₂ vs₂ →
        ∃ w ∈ vs₁, w ∈ vs₂ := by
  classical
  obtain ⟨D₀⟩ := hplanar
  set G := abGraph N D₀
  set aPt := vPt D₀ N.source
  set bPt := vPt D₀ N.sink
  obtain ⟨drawing, hdraw, hpoly⟩ :=
    Graph.polygonal_redrawing G (rawDrawing D₀) (isDrawing_rawDrawing D₀)
  obtain ⟨C₀, p₀, vs₀, hw₀, -⟩ := hconn
  obtain ⟨hpath₀, -⟩ := isPath_of_isChainWalk D₀ hw₀
  have hnone₀ : (none : Option E) ∉ p₀.map Option.some := by simp
  have hex_score : ∃ k : ℕ, ∃ D : List (Option E),
      G.IsPath aPt D bPt ∧ none ∉ D ∧ insideScore drawing D = k :=
    ⟨insideScore drawing (p₀.map Option.some), p₀.map Option.some, hpath₀, hnone₀, rfl⟩
  obtain ⟨D, hD, hnone, hD_eq⟩ := Nat.find_spec hex_score
  have hmin : ∀ D', G.IsPath aPt D' bPt → none ∉ D' →
      insideScore drawing D ≤ insideScore drawing D' := by
    intro D' hD' hnone'
    rw [hD_eq]
    exact Nat.find_min' hex_score ⟨D', hD', hnone', rfl⟩
  obtain ⟨u_src, w_snk, p, vs, hsrc_eq, hsnk_eq, hD_map, hw_raw, hverts_D⟩ :=
    exists_isChainWalk_of_isPath D₀ hD hnone
  have hu_src : u_src = N.source := (vPt_injective D₀ hsrc_eq).symm
  have hw_snk : w_snk = N.sink := (vPt_injective D₀ hsnk_eq).symm
  subst hu_src hw_snk
  refine ⟨p, vs, hw_raw, ?_⟩
  intro j₁ j₂ hj₁ hj₁₂ hj₂ p₁ p₂ vs₁ vs₂ hw₁ hw₂
  by_contra hno_inter
  simp only [not_exists, not_and] at hno_inter
  set v₁ := vs[j₁]'(by omega)
  set v₂ := vs[j₂]'(by omega)
  set u₁ := vPt D₀ v₁
  set u₂ := vPt D₀ v₂
  set W₁ := p₁.map Option.some
  set W₂ := p₂.map Option.some
  obtain ⟨hW₁, hverts_W₁⟩ := isPath_of_isChainWalk D₀ hw₁
  obtain ⟨hW₂, hverts_W₂⟩ := isPath_of_isChainWalk D₀ hw₂
  have hdisj_W : Disjoint (G.walkVertices u₁ W₁) (G.walkVertices aPt W₂) := by
    rw [Set.disjoint_left, hverts_W₁, hverts_W₂]
    rintro z ⟨w₁, hw₁_mem, rfl⟩ ⟨w₂, hw₂_mem, heq⟩
    have hw_eq : w₁ = w₂ := vPt_injective D₀ heq.symm
    exact hno_inter w₁ hw₁_mem (hw_eq ▸ hw₂_mem)
  obtain ⟨h0_vs, hvs0⟩ := chainWalk_head_eq hw_raw
  obtain ⟨hl_vs, hvsl⟩ := chainWalk_last_eq hw_raw
  have hnodup_vs := hw_raw.2.2.2.1
  have hj₂_vs : j₂ < vs.length := by omega
  have hw_left := isChainWalk_take hw_raw j₂ hj₂_vs
  have hw_right := isChainWalk_drop hw_raw j₂ hj₂_vs
  set D_left := (p.take j₂).map Option.some
  set D_right := (p.drop j₂).map Option.some
  obtain ⟨hD_left, hverts_left⟩ := isPath_of_isChainWalk D₀ hw_left
  obtain ⟨hD_right, hverts_right⟩ := isPath_of_isChainWalk D₀ hw_right
  have hD_split : D = D_left ++ D_right := by
    rw [hD_map, ← List.map_append, List.take_append_drop]
  have hM_u₂ : ∀ z ∈ G.walkVertices aPt D_left, z ∈ G.walkVertices u₂ D_right → z = u₂ := by
    rw [hverts_left, hverts_right]
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hxy' : x = y := vPt_injective D₀ hxy.symm
    subst hxy'
    obtain ⟨ix, hix, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨iy, hiy, hEq⟩ := List.getElem_of_mem hy
    simp only [List.length_take] at hix
    simp only [List.length_drop] at hiy
    rw [List.getElem_take] at hEq
    rw [List.getElem_drop] at hEq
    have hidx_eq : ix = j₂ + iy :=
      (List.Nodup.getElem_inj_iff hnodup_vs).mp hEq.symm
    have hix_j₂ : ix = j₂ := by omega
    simp [u₂, v₂, List.getElem_take, hix_j₂]
  have hverts_D_union :
      G.walkVertices aPt D = G.walkVertices aPt D_left ∪ G.walkVertices u₂ D_right := by
    ext z
    rw [hD_split]
    constructor
    · intro hz
      rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
      · exact Or.inl Graph.mem_walkVertices_self
      rw [Graph.coveredVertices_append] at hcov
      rcases hcov with h1 | h2
      · exact Or.inl (Graph.mem_walkVertices_of_mem_covered h1)
      · exact Or.inr (Graph.mem_walkVertices_of_mem_covered h2)
    · rintro (hz | hz)
      · exact Graph.walkVertices_mono (List.subset_append_left _ _) hz
      · rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
        · exact Graph.walkVertices_mono (List.subset_append_left _ _) hD_left.target_mem_walkVertices
        · exact Graph.mem_walkVertices_of_mem_covered
            (Graph.coveredVertices_mono (List.subset_append_right _ _) hcov)
  -- Step A: Extract ear `K₁ ⊆ W₁` between `D_left \ {aPt, u₂}` and `D_right \ {u₂}`.
  set S₁ : Set Plane := G.walkVertices aPt D_left \ {aPt, u₂}
  set S₂ : Set Plane := G.walkVertices u₂ D_right \ {u₂}
  have hS₁₂_disj : Disjoint S₁ S₂ := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    exact hz₂.2 (hM_u₂ z hz₁.1 hz₂.1)
  have hu₁_S₁ : u₁ ∈ S₁ := by
    refine ⟨?_, ?_⟩
    · rw [hverts_left]
      refine ⟨v₁, ?_, rfl⟩
      have hj₁_take : j₁ < (vs.take (j₂ + 1)).length := by
        simp only [List.length_take]; omega
      have hget : (vs.take (j₂ + 1))[j₁]'hj₁_take = v₁ := by simp [v₁]
      exact hget ▸ List.getElem_mem hj₁_take
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨?_, ?_⟩
      · intro hEq
        have hv₁_src : vs[j₁]'(by omega) = vs[0]'h0_vs :=
          (vPt_injective D₀ hEq).trans hvs0.symm
        have := (List.Nodup.getElem_inj_iff hnodup_vs).mp hv₁_src
        omega
      · intro hEq
        have hv₁_v₂ : vs[j₁]'(by omega) = vs[j₂]'hj₂_vs := vPt_injective D₀ hEq
        have := (List.Nodup.getElem_inj_iff hnodup_vs).mp hv₁_v₂
        omega
  have hbPt_S₂ : bPt ∈ S₂ := by
    refine ⟨hD_right.target_mem_walkVertices, ?_⟩
    rw [Set.mem_singleton_iff]
    intro hEq
    have hsnk_v₂ : vs[p.length]'hl_vs = vs[j₂]'hj₂_vs :=
      hvsl.trans (vPt_injective D₀ hEq)
    have := (List.Nodup.getElem_inj_iff hnodup_vs).mp hsnk_v₂
    have := hw_raw.1
    omega
  have hW₁_part : ∀ z ∈ G.walkVertices u₁ W₁, z ∈ G.walkVertices aPt D →
      z ∈ S₁ ∨ z ∈ S₂ := by
    intro z hzW₁ hzD
    have hza : z ≠ aPt := fun hEq =>
      Set.disjoint_left.mp hdisj_W hzW₁ (hEq ▸ Graph.mem_walkVertices_self)
    have hzu₂ : z ≠ u₂ := fun hEq =>
      Set.disjoint_left.mp hdisj_W hzW₁ (hEq ▸ hW₂.target_mem_walkVertices)
    rw [hverts_D_union] at hzD
    rcases hzD with hzL | hzR
    · exact Or.inl ⟨hzL, by simp [hza, hzu₂]⟩
    · exact Or.inr ⟨hzR, by simp [hzu₂]⟩
  obtain ⟨x₁, hx₁S₁, y₁, hy₁S₂, K₁, hK₁W₁, hx₁y₁, hK₁, hK₁_sub_W₁, hint₁⟩ :=
    extract_ear hW₁ hu₁_S₁ hbPt_S₂ hS₁₂_disj hW₁_part
  have hx₁_not_R : x₁ ∉ G.walkVertices u₂ D_right := fun h =>
    hx₁S₁.2 (Or.inr (hM_u₂ x₁ hx₁S₁.1 h))
  have hy₁_not_L : y₁ ∉ G.walkVertices aPt D_left := fun h =>
    hy₁S₂.2 (hM_u₂ y₁ h hy₁S₂.1)
  have hK₁_not_D : ∀ g ∈ K₁, g ∉ D := by
    rw [hD_split]
    exact ear_edges_notMem_of_split hD_left hD_right hK₁ hx₁_not_R hy₁_not_L
      (hverts_D_union ▸ hint₁)
  have hK₁_new : ∀ g ∈ K₁, g ∉ none :: D := by
    intro g hgK₁ hg
    rcases List.mem_cons.mp hg with rfl | hgD
    · have hgW₁ : (none : Option E) ∈ W₁ := hK₁W₁ hgK₁
      simp [W₁] at hgW₁
    · exact hK₁_not_D g hgK₁ hgD
  -- Step B: Split `D_left` at `x₁` and `D_right` at `y₁`, and apply `hc.split_aux`.
  obtain ⟨X, Y₁, hXY₁, hX, hY₁, hMX⟩ := hD_left.split_meet hx₁S₁.1
  obtain ⟨Y₂, Z, hY₂Z, hY₂, hZ, hMZ⟩ := hD_right.split_meet hy₁S₂.1
  have hD_left_eq : D_left = X ++ Y₁ := hXY₁
  have hD_right_eq : D_right = Y₂ ++ Z := hY₂Z
  set Y := Y₁ ++ Y₂
  have hY₁_sub_L : G.walkVertices x₁ Y₁ ⊆ G.walkVertices aPt D_left := by
    intro z hz
    rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
    · exact hx₁S₁.1
    · rw [hD_left_eq]
      exact Graph.mem_walkVertices_of_mem_covered
        (Graph.coveredVertices_mono (List.subset_append_right _ _) hcov)
  have hX_sub_L : G.walkVertices aPt X ⊆ G.walkVertices aPt D_left := by
    rw [hD_left_eq]
    exact Graph.walkVertices_mono (List.subset_append_left _ _)
  have hY₂_sub_R : G.walkVertices u₂ Y₂ ⊆ G.walkVertices u₂ D_right := by
    rw [hD_right_eq]
    exact Graph.walkVertices_mono (List.subset_append_left _ _)
  have hZ_sub_R : G.walkVertices y₁ Z ⊆ G.walkVertices u₂ D_right := by
    intro z hz
    rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
    · exact hy₁S₂.1
    · rw [hD_right_eq]
      exact Graph.mem_walkVertices_of_mem_covered
        (Graph.coveredVertices_mono (List.subset_append_right _ _) hcov)
  have hY : G.IsPath x₁ Y y₁ :=
    hY₁.append hY₂ fun z hz₁ hz₂ => hM_u₂ z (hY₁_sub_L hz₁) (hY₂_sub_R hz₂)
  have hY_verts : G.walkVertices x₁ Y = G.walkVertices x₁ Y₁ ∪ G.walkVertices u₂ Y₂ := by
    ext z
    constructor
    · intro hz
      rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
      · exact Or.inl Graph.mem_walkVertices_self
      rw [Graph.coveredVertices_append] at hcov
      rcases hcov with h1 | h2
      · exact Or.inl (Graph.mem_walkVertices_of_mem_covered h1)
      · exact Or.inr (Graph.mem_walkVertices_of_mem_covered h2)
    · rintro (hz | hz)
      · exact Graph.walkVertices_mono (List.subset_append_left _ _) hz
      · rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
        · exact Graph.walkVertices_mono (List.subset_append_left _ _) hY₁.target_mem_walkVertices
        · exact Graph.mem_walkVertices_of_mem_covered
            (Graph.coveredVertices_mono (List.subset_append_right _ _) hcov)
  have hYZ_verts : G.walkVertices x₁ (Y ++ Z) = G.walkVertices x₁ Y ∪ G.walkVertices y₁ Z := by
    ext z
    constructor
    · intro hz
      rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
      · exact Or.inl Graph.mem_walkVertices_self
      rw [Graph.coveredVertices_append] at hcov
      rcases hcov with h1 | h2
      · exact Or.inl (Graph.mem_walkVertices_of_mem_covered h1)
      · exact Or.inr (Graph.mem_walkVertices_of_mem_covered h2)
    · rintro (hz | hz)
      · exact Graph.walkVertices_mono (List.subset_append_left _ _) hz
      · rcases Graph.mem_walkVertices_iff.mp hz with rfl | hcov
        · exact Graph.walkVertices_mono (List.subset_append_left _ _) hY.target_mem_walkVertices
        · exact Graph.mem_walkVertices_of_mem_covered
            (Graph.coveredVertices_mono (List.subset_append_right _ _) hcov)
  have hM1_XYZ : ∀ z ∈ G.walkVertices aPt X, z ∈ G.walkVertices x₁ (Y ++ Z) → z = x₁ := by
    intro z hzX hzYZ
    rw [hYZ_verts, hY_verts] at hzYZ
    rcases hzYZ with (hzY₁ | hzY₂) | hzZ
    · exact hMX z hzX hzY₁
    · exfalso
      have hzu₂ : z = u₂ := hM_u₂ z (hX_sub_L hzX) (hY₂_sub_R hzY₂)
      have hzx₁ : z = x₁ := hMX z hzX (hzu₂ ▸ hY₁.target_mem_walkVertices)
      exact hx₁S₁.2 (Or.inr (hzx₁.symm.trans hzu₂))
    · exfalso
      have hzu₂ : z = u₂ := hM_u₂ z (hX_sub_L hzX) (hZ_sub_R hzZ)
      have hzx₁ : z = x₁ := hMX z hzX (hzu₂ ▸ hY₁.target_mem_walkVertices)
      exact hx₁S₁.2 (Or.inr (hzx₁.symm.trans hzu₂))
  have hM2_XYZ : ∀ z ∈ G.walkVertices x₁ Y, z ∈ G.walkVertices y₁ Z → z = y₁ := by
    intro z hzY hzZ
    rw [hY_verts] at hzY
    rcases hzY with hzY₁ | hzY₂
    · have hzu₂ : z = u₂ := hM_u₂ z (hY₁_sub_L hzY₁) (hZ_sub_R hzZ)
      exact hMZ z (hzu₂ ▸ Graph.mem_walkVertices_self) hzZ
    · exact hMZ z hzY₂ hzZ
  have hD_XYZ : D = X ++ (Y ++ Z) := by
    rw [hD_split, hD_left_eq, hD_right_eq]
    simp [Y, List.append_assoc]
  have hlink_none : G.IsLink none aPt bPt := Or.inl ⟨rfl, rfl⟩
  have hc : G.IsCycleThrough none aPt bPt D := ⟨hlink_none, hD, hnone⟩
  obtain ⟨hZX, hperm_Y_ZX, hmeet_Y_ZX⟩ :=
    hc.split_aux hD_XYZ hX hY hZ hx₁y₁ hM1_XYZ hM2_XYZ
  -- Step C: Extract ear `K₂ ⊆ W₂` between `(Z ++ none :: X) \ {x₁, y₁}` and `Y \ {x₁, y₁}`.
  set ZX := Z ++ none :: X
  have hverts_D_Y_ZX :
      G.walkVertices aPt D = G.walkVertices x₁ Y ∪ G.walkVertices y₁ ZX := by
    have hround := hc.walkVertices_round
    have hcov_D : G.walkVertices aPt (D ++ [none]) = G.coveredVertices (D ++ [none]) :=
      hc.isWalk_round.walkVertices_eq_covered (by simp)
    have hcov_Y : G.walkVertices x₁ Y = G.coveredVertices Y :=
      hY.isWalk.walkVertices_eq_covered (hY.ne_nil hx₁y₁)
    have hcov_ZX : G.walkVertices y₁ ZX = G.coveredVertices ZX :=
      hZX.isWalk.walkVertices_eq_covered (hZX.ne_nil hx₁y₁.symm)
    rw [← hround, hcov_D, hcov_Y, hcov_ZX, ← Graph.coveredVertices_append]
    have hperm' : (D ++ [none]).Perm (Y ++ ZX) :=
      (List.perm_append_singleton none D).trans hperm_Y_ZX.symm
    ext z
    simp only [Graph.mem_coveredVertices_iff]
    exact ⟨fun ⟨e, he, hz⟩ => ⟨e, hperm'.mem_iff.mp he, hz⟩,
      fun ⟨e, he, hz⟩ => ⟨e, hperm'.mem_iff.mpr he, hz⟩⟩
  set T₁ : Set Plane := G.walkVertices y₁ ZX \ {x₁, y₁}
  set T₂ : Set Plane := G.walkVertices x₁ Y \ {x₁, y₁}
  have hT₁₂_disj : Disjoint T₁ T₂ := by
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    exact hz₁.2 (hmeet_Y_ZX z hz₂.1 hz₁.1)
  have haPt_T₁ : aPt ∈ T₁ := by
    refine ⟨?_, ?_⟩
    · refine Graph.mem_walkVertices_of_mem_covered ⟨none, ?_, hlink_none.inc_left⟩
      exact List.mem_append_right _ List.mem_cons_self
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun hEq => hx₁S₁.2 (Or.inl hEq.symm),
        fun hEq => hy₁_not_L (hEq ▸ Graph.mem_walkVertices_self)⟩
  have hu₂_T₂ : u₂ ∈ T₂ := by
    refine ⟨?_, ?_⟩
    · rw [hY_verts]
      exact Or.inl hY₁.target_mem_walkVertices
    · rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun hEq => hx₁S₁.2 (Or.inr hEq.symm),
        fun hEq => hy₁S₂.2 hEq.symm⟩
  have hW₂_part : ∀ z ∈ G.walkVertices aPt W₂, z ∈ G.walkVertices aPt D →
      z ∈ T₁ ∨ z ∈ T₂ := by
    intro z hzW₂ hzD
    have hzx₁ : z ≠ x₁ := fun hEq =>
      Set.disjoint_left.mp hdisj_W (hK₁_sub_W₁ (hEq ▸ Graph.mem_walkVertices_self)) hzW₂
    have hzy₁ : z ≠ y₁ := fun hEq =>
      Set.disjoint_left.mp hdisj_W (hK₁_sub_W₁ (hEq ▸ hK₁.target_mem_walkVertices)) hzW₂
    rw [hverts_D_Y_ZX] at hzD
    rcases hzD with hzY | hzZX
    · exact Or.inr ⟨hzY, by simp [hzx₁, hzy₁]⟩
    · exact Or.inl ⟨hzZX, by simp [hzx₁, hzy₁]⟩
  obtain ⟨x₂, hx₂T₁, y₂, hy₂T₂, K₂, hK₂W₂, hx₂y₂, hK₂, hK₂_sub_W₂, hint₂⟩ :=
    extract_ear hW₂ haPt_T₁ hu₂_T₂ hT₁₂_disj hW₂_part
  have hx₂_not_Y : x₂ ∉ G.walkVertices x₁ Y := fun h =>
    hx₂T₁.2 (hmeet_Y_ZX x₂ h hx₂T₁.1)
  have hy₂_not_ZX : y₂ ∉ G.walkVertices y₁ ZX := fun h =>
    hy₂T₂.2 (hmeet_Y_ZX y₂ hy₂T₂.1 h)
  have hK₂_not_ZX_Y : ∀ g ∈ K₂, g ∉ ZX ++ Y :=
    ear_edges_notMem_of_split hZX hY hK₂ hx₂_not_Y hy₂_not_ZX
      (by
        intro z hz h1 h2 hmem
        refine hint₂ z hz h1 h2 ?_
        rw [hverts_D_Y_ZX, Set.union_comm]
        exact hmem)
  have hK₂_not_Y_ZX : ∀ g ∈ K₂, g ∉ Y ++ ZX :=
    fun g hgK₂ hg => hK₂_not_ZX_Y g hgK₂ ((List.perm_append_comm).mem_iff.mp hg)
  have hK₂_new : ∀ g ∈ K₂, g ∉ none :: D :=
    fun g hgK₂ hg => hK₂_not_Y_ZX g hgK₂ (hperm_Y_ZX.mem_iff.mpr hg)
  -- Step D: Both `K₁` and `K₂` lie in `outside J` and alternate, so they intersect.
  set J := Graph.edgesCover drawing (none :: D)
  have hx₁_D : x₁ ∈ G.walkVertices aPt D := by
    rw [hverts_D_union]; exact Or.inl hx₁S₁.1
  have hy₁_D : y₁ ∈ G.walkVertices aPt D := by
    rw [hverts_D_union]; exact Or.inr hy₁S₂.1
  have hx₂_D : x₂ ∈ G.walkVertices aPt D := by
    rw [hverts_D_Y_ZX]; exact Or.inr hx₂T₁.1
  have hy₂_D : y₂ ∈ G.walkVertices aPt D := by
    rw [hverts_D_Y_ZX]; exact Or.inl hy₂T₂.1
  have hK₁_out : Graph.edgesCover drawing K₁ \ {x₁, y₁} ⊆ Schoenflies.outside J :=
    ear_subset_outside_of_minimal hdraw hpoly hD hnone hmin hK₁ hx₁y₁ hx₁_D hy₁_D hint₁ hK₁_new
  have hK₂_out : Graph.edgesCover drawing K₂ \ {x₂, y₂} ⊆ Schoenflies.outside J :=
    ear_subset_outside_of_minimal hdraw hpoly hD hnone hmin hK₂ hx₂y₂ hx₂_D hy₂_D hint₂ hK₂_new
  have hnodup_cycle : (none :: D).Nodup :=
    List.nodup_cons.mpr ⟨hc.notMem, hc.isPath.nodup⟩
  have hdisj_Y_ZX : ∀ g ∈ Y, g ∉ ZX := fun g hgY hgZX =>
    (List.nodup_append.mp (hperm_Y_ZX.nodup_iff.mpr hnodup_cycle)).2.2 g hgY g hgZX rfl
  obtain ⟨harc₁, harc₂, hinter_arcs⟩ :=
    hdraw.arcs_of_split hY hZX hx₁y₁ hdisj_Y_ZX hmeet_Y_ZX
  have hunion_arcs :
      Graph.edgesCover drawing Y ∪ Graph.edgesCover drawing ZX = J := by
    rw [← Graph.edgesCover_append, Graph.edgesCover_perm hperm_Y_ZX]
  have hJsep : IsSeparating J := hdraw.cycle_isSeparating hpoly hc
  have hJpoly : IsPolygonal J :=
    hdraw.isPolygonal_edgesCover hpoly hc.isWalk_cons (List.cons_ne_nil _ _)
  have hK₁poly : IsPolygonal (Graph.edgesCover drawing K₁) :=
    hdraw.isPolygonal_edgesCover hpoly hK₁.isWalk (hK₁.ne_nil hx₁y₁)
  have hK₁arc : IsArcBetween (Graph.edgesCover drawing K₁) x₁ y₁ :=
    hdraw.path_isArcBetween hK₁ (hK₁.ne_nil hx₁y₁)
  have hK₂arc : IsArcBetween (Graph.edgesCover drawing K₂) x₂ y₂ :=
    hdraw.path_isArcBetween hK₂ (hK₂.ne_nil hx₂y₂)
  have hK₁J : Graph.edgesCover drawing K₁ ∩ J = {x₁, y₁} :=
    ear_inter_cycle_eq hdraw hc hK₁ hx₁y₁ hx₁_D hy₁_D hint₁ hK₁_new
  have hx₂_arc₂ : x₂ ∈ Graph.edgesCover drawing ZX \ {x₁, y₁} := by
    refine ⟨?_, hx₂T₁.2⟩
    rw [← hdraw.pointSet_pathGraphOf hZX.isWalk (hZX.ne_nil hx₁y₁.symm)]
    exact Graph.vertexSet_subset_pointSet (Graph.pathGraphOf_vertexSet ▸ hx₂T₁.1)
  have hy₂_arc₁ : y₂ ∈ Graph.edgesCover drawing Y \ {x₁, y₁} := by
    refine ⟨?_, hy₂T₂.2⟩
    rw [← hdraw.pointSet_pathGraphOf hY.isWalk (hY.ne_nil hx₁y₁)]
    exact Graph.vertexSet_subset_pointSet (Graph.pathGraphOf_vertexSet ▸ hy₂T₂.1)
  have hinter_K₁₂ : (Graph.edgesCover drawing K₁ ∩ Graph.edgesCover drawing K₂).Nonempty :=
    alternating_crosscuts_outside_inter hJsep hJpoly hK₁poly harc₁ harc₂.reverse
      hunion_arcs hinter_arcs hK₁arc hK₁J hK₁_out hK₂arc hK₂_out hx₂_arc₂ hy₂_arc₁
  obtain ⟨z, hzK₁, hzK₂⟩ := edgesCover_inter_walkVertices_nonempty hdraw hK₁ hK₂ hinter_K₁₂
  exact Set.disjoint_left.mp hdisj_W (hK₁_sub_W₁ hzK₁) (hK₂_sub_W₂ hzK₂)

