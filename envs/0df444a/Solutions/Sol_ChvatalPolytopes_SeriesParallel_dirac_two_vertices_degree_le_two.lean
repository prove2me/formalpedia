-- Prove2me | solution 1 for ChvatalPolytopes.SeriesParallel.dirac_two_vertices_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T09:13:45.321933+00:00
-- url     : https://prove2.me/submissions/30679781-0100-4d55-91dd-b4e85f8ff993

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel

namespace SolChvatalDirac

set_option linter.unusedSectionVars false

open ChvatalPolytopes.SeriesParallel (ContainsK4Homeomorph IsSeriesParallel)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Part 1: K4 Homeomorph for 4-Cliques, Subgraphs, Induced Subgraphs, and Suppression -/

lemma containsK4Homeomorph_of_adj4 {G : SimpleGraph V} (b : Fin 4 → V)
    (hadj : ∀ i j : Fin 4, i ≠ j → G.Adj (b i) (b j)) :
    ContainsK4Homeomorph G := by
  have hinj : Function.Injective b := by
    intro i j hij
    by_contra hne
    exact G.ne_of_adj (hadj i j hne) hij
  let p : ∀ i j : Fin 4, G.Walk (b i) (b j) := fun i j =>
    if h : i = j then
      h ▸ SimpleGraph.Walk.nil
    else
      SimpleGraph.Walk.cons (hadj i j h) SimpleGraph.Walk.nil
  have hp_eq : ∀ i j : Fin 4, (h : i < j) →
      p i j = SimpleGraph.Walk.cons (hadj i j (ne_of_lt h)) SimpleGraph.Walk.nil := by
    intro i j h
    dsimp [p]
    rw [dif_neg (ne_of_lt h)]
  refine ⟨b, p, hinj, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hp_eq i j hij]
    exact SimpleGraph.Walk.IsPath.cons (SimpleGraph.Walk.IsPath.nil) (by
      simp [G.ne_of_adj (hadj i j (ne_of_lt hij))])
  · intro i j hij k hk
    rw [hp_eq i j hij] at hk
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with hk | hk
    · exact Or.inl (hinj hk)
    · exact Or.inr (hinj hk)
  · intro i j _ _ hij _ _ v hv _
    rw [hp_eq i j hij] at hv
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩

lemma containsK4Homeomorph_of_clique4 {G : SimpleGraph V} {u v w c : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (huc : G.Adj u c)
    (hvw : G.Adj v w) (hvc : G.Adj v c) (hwc : G.Adj w c) :
    ContainsK4Homeomorph G := by
  let b : Fin 4 → V := fun i =>
    if i = 0 then u else if i = 1 then v else if i = 2 then w else c
  apply containsK4Homeomorph_of_adj4 b
  intro i j hij
  fin_cases i <;> fin_cases j <;> dsimp [b] <;> first
    | exact False.elim (hij rfl)
    | exact huv
    | exact huv.symm
    | exact huw
    | exact huw.symm
    | exact huc
    | exact huc.symm
    | exact hvw
    | exact hvw.symm
    | exact hvc
    | exact hvc.symm
    | exact hwc
    | exact hwc.symm

lemma isSeriesParallel_mono {G G' : SimpleGraph V} (hle : G' ≤ G) (hG : IsSeriesParallel G) :
    IsSeriesParallel G' := by
  intro ⟨b, p, hinj, hpath, hbranch, hinter⟩
  apply hG
  let f : G' →g G := SimpleGraph.Hom.ofLE hle
  refine ⟨fun i => f (b i), fun i j => (p i j).map f, hinj, ?_, ?_, ?_⟩
  · intro i j hij
    dsimp
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_map]
    exact (List.nodup_map_iff_inj_on (hpath i j hij).support_nodup).mpr (fun x _ y _ h => h)
  · intro i j hij k hk
    dsimp at hk
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hk
    rcases hk with ⟨x, hx, hxk⟩
    dsimp [f] at hxk
    subst hxk
    exact hbranch i j hij k hx
  · intro i j i' j' hij hij' hne v hv hv'
    dsimp at hv hv'
    rw [SimpleGraph.Walk.support_map] at hv hv'
    have hv1 : v ∈ (p i j).support := by simpa [f] using hv
    have hv2 : v ∈ (p i' j').support := by simpa [f] using hv'
    exact hinter i j i' j' hij hij' hne v hv1 hv2

/-- Induced subgraph on `{x : V // x ≠ u}`. -/
abbrev induceNe (G : SimpleGraph V) (u : V) : SimpleGraph {x : V // x ≠ u} :=
  G.comap Subtype.val

instance (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    DecidableRel (induceNe G u).Adj := by
  intro a b
  change Decidable (G.Adj a.1 b.1)
  infer_instance

lemma isSeriesParallel_induceNe {G : SimpleGraph V} (u : V) (hG : IsSeriesParallel G) :
    IsSeriesParallel (induceNe G u) := by
  intro ⟨b, p, hinj, hpath, hbranch, hinter⟩
  apply hG
  let f : induceNe G u →g G :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  have hfinj : Function.Injective f := Subtype.val_injective
  refine ⟨fun i => f (b i), fun i j => (p i j).map f, fun i j h => hinj (hfinj h), ?_, ?_, ?_⟩
  · intro i j hij
    dsimp
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_map]
    exact (List.nodup_map_iff_inj_on (hpath i j hij).support_nodup).mpr
      (fun x _ y _ h => hfinj h)
  · intro i j hij k hk
    dsimp at hk
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hk
    rcases hk with ⟨x, hx, hxk⟩
    have hxb : x = b k := hfinj hxk
    subst hxb
    exact hbranch i j hij k hx
  · intro i j i' j' hij hij' hne v hv hv'
    dsimp at hv hv'
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hv hv'
    rcases hv with ⟨xr, hxr, hxv⟩
    rcases hv' with ⟨yr, hyr, hyv⟩
    have hy_eq : yr = xr := hfinj (hyv.trans hxv.symm)
    obtain ⟨k, hk⟩ := hinter i j i' j' hij hij' hne xr hxr (hy_eq ▸ hyr)
    exact ⟨k, hxv.symm.trans (congrArg f hk)⟩

/-- Suppressing a vertex `u` between two of its neighbors `v` and `w`: delete `u` and add the
edge `vw`. -/
def suppress (G : SimpleGraph V) (u v w : V) : SimpleGraph {x : V // x ≠ u} where
  Adj a b := a ≠ b ∧ (G.Adj a.1 b.1 ∨ (a.1 = v ∧ b.1 = w) ∨ (a.1 = w ∧ b.1 = v))
  symm := ⟨fun a b h => by
    refine ⟨h.1.symm, ?_⟩
    rcases h.2 with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl h1.symm
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance (G : SimpleGraph V) [DecidableRel G.Adj] (u v w : V) :
    DecidableRel (suppress G u v w).Adj := by
  intro a b
  unfold suppress
  dsimp
  infer_instance

def liftWalk {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) :
    ∀ {a b : {x : V // x ≠ u}}, (suppress G u v w).Walk a b → G.Walk a.1 b.1
  | _, _, SimpleGraph.Walk.nil => SimpleGraph.Walk.nil
  | a, _, SimpleGraph.Walk.cons (v := c) h W =>
    if hG : G.Adj a.1 c.1 then
      SimpleGraph.Walk.cons hG (liftWalk huv huw W)
    else
      have hau : G.Adj a.1 u := by
        rcases h.2 with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact False.elim (hG h1)
        · exact huv.symm
        · exact huw.symm
      have huc : G.Adj u c.1 := by
        rcases h.2 with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact False.elim (hG h1)
        · exact huw
        · exact huv
      SimpleGraph.Walk.cons hau (SimpleGraph.Walk.cons huc (liftWalk huv huw W))

lemma mem_support_liftWalk {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) :
    ∀ {a b : {x : V // x ≠ u}} (W : (suppress G u v w).Walk a b) {z : V},
      z ∈ (liftWalk huv huw W).support →
        (∃ x ∈ W.support, x.1 = z) ∨
        (z = u ∧ v ≠ w ∧ (∃ x ∈ W.support, x.1 = v) ∧ (∃ y ∈ W.support, y.1 = w))
  | a, _, SimpleGraph.Walk.nil, z, hz => by
    simp only [liftWalk, SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz
    exact Or.inl ⟨a, by simp, rfl⟩
  | a, b, SimpleGraph.Walk.cons (v := c) h W, z, hz => by
    dsimp [liftWalk] at hz
    split_ifs at hz with hG
    · simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact Or.inl ⟨a, by simp, rfl⟩
      · rcases mem_support_liftWalk huv huw W hz with
          ⟨x, hx, rfl⟩ | ⟨rfl, hvw, ⟨x, hx, hxv⟩, ⟨y, hy, hyw⟩⟩
        · exact Or.inl ⟨x, by simp [hx], rfl⟩
        · exact Or.inr ⟨rfl, hvw, ⟨x, by simp [hx], hxv⟩, ⟨y, by simp [hy], hyw⟩⟩
    · simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · exact Or.inl ⟨a, by simp, rfl⟩
      · rcases h.2 with h1 | ⟨hv, hw⟩ | ⟨hw, hv⟩
        · exact False.elim (hG h1)
        · have hvw : v ≠ w := fun heq => h.1 (Subtype.ext (hv.trans (heq.trans hw.symm)))
          exact Or.inr ⟨rfl, hvw, ⟨a, by simp, hv⟩, ⟨c, by simp, hw⟩⟩
        · have hvw : v ≠ w := fun heq => h.1 (Subtype.ext (hw.trans (heq.symm.trans hv.symm)))
          exact Or.inr ⟨rfl, hvw, ⟨c, by simp, hv⟩, ⟨a, by simp, hw⟩⟩
      · rcases mem_support_liftWalk huv huw W hz with
          ⟨x, hx, rfl⟩ | ⟨rfl, hvw, ⟨x, hx, hxv⟩, ⟨y, hy, hyw⟩⟩
        · exact Or.inl ⟨x, by simp [hx], rfl⟩
        · exact Or.inr ⟨rfl, hvw, ⟨x, by simp [hx], hxv⟩, ⟨y, by simp [hy], hyw⟩⟩

lemma nodup_support_liftWalk {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) :
    ∀ {a b : {x : V // x ≠ u}} (W : (suppress G u v w).Walk a b),
      W.support.Nodup → (liftWalk huv huw W).support.Nodup
  | a, _, SimpleGraph.Walk.nil, _ => by
    simp [liftWalk]
  | a, b, SimpleGraph.Walk.cons (v := c) h W, hnodup => by
    rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
    rcases hnodup with ⟨ha_not, hnodup'⟩
    have ih := nodup_support_liftWalk huv huw W hnodup'
    have ha_not_lift : a.1 ∉ (liftWalk huv huw W).support := by
      intro ha_mem
      rcases mem_support_liftWalk huv huw W ha_mem with ⟨x, hx, hxa⟩ | ⟨hau, _, _, _⟩
      · exact ha_not (Subtype.ext hxa ▸ hx)
      · exact a.2 hau
    dsimp [liftWalk]
    split_ifs with hG
    · rw [SimpleGraph.Walk.support_cons, List.nodup_cons]
      exact ⟨ha_not_lift, ih⟩
    · rw [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_cons,
        List.nodup_cons, List.nodup_cons]
      have hu_not_lift : u ∉ (liftWalk huv huw W).support := by
        intro hu_mem
        rcases mem_support_liftWalk huv huw W hu_mem with
          ⟨x, _, hxu⟩ | ⟨_, _, ⟨x, hx, hxv⟩, ⟨y, hy, hyw⟩⟩
        · exact x.2 hxu
        · rcases h.2 with h1 | ⟨hav, _⟩ | ⟨haw, _⟩
          · exact hG h1
          · exact ha_not (Subtype.ext (hxv.trans hav.symm) ▸ hx)
          · exact ha_not (Subtype.ext (hyw.trans haw.symm) ▸ hy)
      refine ⟨?_, hu_not_lift, ih⟩
      simp only [List.mem_cons, not_or]
      exact ⟨a.2, ha_not_lift⟩

lemma pair_eq_of_mem_two {α : Type*} [LinearOrder α] {k₁ k₂ i j i' j' : α}
    (hij : i < j) (hij' : i' < j') (hk₁₂ : k₁ ≠ k₂)
    (h1 : k₁ = i ∨ k₁ = j) (h2 : k₂ = i ∨ k₂ = j)
    (h3 : k₁ = i' ∨ k₁ = j') (h4 : k₂ = i' ∨ k₂ = j') :
    (i, j) = (i', j') := by
  rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2
  · exact False.elim (hk₁₂ h2.symm)
  · subst h2
    rcases h3 with rfl | rfl <;> rcases h4 with h4 | h4
    · exact False.elim (hk₁₂ h4.symm)
    · subst h4; rfl
    · subst h4; exact False.elim (lt_asymm hij hij')
    · exact False.elim (hk₁₂ h4.symm)
  · subst h2
    rcases h3 with rfl | rfl <;> rcases h4 with h4 | h4
    · exact False.elim (hk₁₂ h4.symm)
    · subst h4; exact False.elim (lt_asymm hij hij')
    · subst h4; rfl
    · exact False.elim (hk₁₂ h4.symm)
  · exact False.elim (hk₁₂ h2.symm)

lemma isSeriesParallel_suppress {G : SimpleGraph V} [DecidableRel G.Adj] {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hG : IsSeriesParallel G) :
    IsSeriesParallel (suppress G u v w) := by
  intro ⟨b', p', hinj', hpath', hbranch', hinter'⟩
  apply hG
  let b : Fin 4 → V := fun i => (b' i).1
  let p : ∀ i j : Fin 4, G.Walk (b i) (b j) := fun i j => liftWalk huv huw (p' i j)
  have hinj : Function.Injective b := fun i j hij => hinj' (Subtype.ext hij)
  refine ⟨b, p, hinj, ?_, ?_, ?_⟩
  · intro i j hij
    rw [SimpleGraph.Walk.isPath_def]
    exact nodup_support_liftWalk huv huw (p' i j) (hpath' i j hij).support_nodup
  · intro i j hij k hk
    rcases mem_support_liftWalk huv huw (p' i j) hk with ⟨x, hx, hxb⟩ | ⟨hbu, _, _, _⟩
    · have hxk : x = b' k := Subtype.ext hxb
      subst hxk
      exact hbranch' i j hij k hx
    · exact False.elim ((b' k).2 hbu)
  · intro i j i' j' hij hij' hne z hz hz'
    rcases mem_support_liftWalk huv huw (p' i j) hz with
      ⟨xr, hxr, hxz⟩ | ⟨hz_u, hvw, ⟨x₁, hx₁, hx₁v⟩, ⟨y₁, hy₁, hy₁w⟩⟩
    · rcases mem_support_liftWalk huv huw (p' i' j') hz' with ⟨yr, hyr, hyz⟩ | ⟨hz_u, _, _, _⟩
      · have hy_eq : yr = xr := Subtype.ext (hyz.trans hxz.symm)
        obtain ⟨k, hk⟩ := hinter' i j i' j' hij hij' hne xr hxr (hy_eq ▸ hyr)
        exact ⟨k, hxz.symm.trans (congrArg Subtype.val hk)⟩
      · exact False.elim (xr.2 (hxz.trans hz_u))
    · rcases mem_support_liftWalk huv huw (p' i' j') hz' with
        ⟨xr, _, hxz⟩ | ⟨_, _, ⟨x₂, hx₂, hx₂v⟩, ⟨y₂, hy₂, hy₂w⟩⟩
      · exact False.elim (xr.2 (hxz.trans hz_u))
      · have hx₁₂ : x₂ = x₁ := Subtype.ext (hx₂v.trans hx₁v.symm)
        have hy₁₂ : y₂ = y₁ := Subtype.ext (hy₂w.trans hy₁w.symm)
        obtain ⟨k₁, hk₁⟩ := hinter' i j i' j' hij hij' hne x₁ hx₁ (hx₁₂ ▸ hx₂)
        obtain ⟨k₂, hk₂⟩ := hinter' i j i' j' hij hij' hne y₁ hy₁ (hy₁₂ ▸ hy₂)
        have hk₁_ij : k₁ = i ∨ k₁ = j := hbranch' i j hij k₁ (hk₁ ▸ hx₁)
        have hk₂_ij : k₂ = i ∨ k₂ = j := hbranch' i j hij k₂ (hk₂ ▸ hy₁)
        have hk₁_ij' : k₁ = i' ∨ k₁ = j' := hbranch' i' j' hij' k₁ (hk₁ ▸ hx₁₂ ▸ hx₂)
        have hk₂_ij' : k₂ = i' ∨ k₂ = j' := hbranch' i' j' hij' k₂ (hk₂ ▸ hy₁₂ ▸ hy₂)
        have hk₁₂ : k₁ ≠ k₂ := by
          intro heq
          apply hvw
          rw [← hx₁v, ← hy₁w, hk₁, hk₂, heq]
        exact False.elim (hne (pair_eq_of_mem_two hij hij' hk₁₂ hk₁_ij hk₂_ij hk₁_ij' hk₂_ij'))

/-! ### Part 2: Degree Lower Bounds under Graph Operations -/

lemma degree_deleteEdges_le_of_ne (G : SimpleGraph V) [DecidableRel G.Adj] {r u x : V}
    (hxr : x ≠ r) (hxu : x ≠ u) :
    G.degree x ≤ (G.deleteEdges {s(r, u)}).degree x := by
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  refine Finset.card_le_card (fun y hy => ?_)
  rw [SimpleGraph.mem_neighborFinset] at hy ⊢
  rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
  refine ⟨hy, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact hxr rfl
  · exact hxu rfl

lemma degree_le_deleteEdges_add_one (G : SimpleGraph V) [DecidableRel G.Adj] (r u : V) :
    G.degree r ≤ (G.deleteEdges {s(r, u)}).degree r + 1 := by
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : G.neighborFinset r ⊆ insert u ((G.deleteEdges {s(r, u)}).neighborFinset r) := by
    intro y hy
    rw [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
    rw [SimpleGraph.mem_neighborFinset] at hy
    by_cases hyu : y = u
    · exact Or.inl hyu
    · refine Or.inr ?_
      rw [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, Sym2.eq_iff]
      refine ⟨hy, ?_⟩
      rintro (⟨_, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hyu rfl
      · exact G.ne_of_adj hy rfl
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

lemma card_edgeFinset_deleteEdges_lt (G : SimpleGraph V) [DecidableRel G.Adj] {r u : V}
    (hadj : G.Adj r u) :
    (G.deleteEdges {s(r, u)}).edgeFinset.card < G.edgeFinset.card := by
  refine Finset.card_lt_card ⟨?_, ?_⟩
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he ⊢
    exact SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _) he
  · intro hsub
    have hmem : s(r, u) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hadj
    have hmem' := hsub hmem
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff] at hmem'
    exact hmem'.2 (Set.mem_singleton _)

lemma degree_induceNe_le_of_not_adj (G : SimpleGraph V) [DecidableRel G.Adj] {u : V}
    (x : {z : V // z ≠ u}) (hnadj : ¬ G.Adj u x.1) :
    G.degree x.1 ≤ (induceNe G u).degree x := by
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  let φ : V → {z : V // z ≠ u} := fun y => if h : y ≠ u then ⟨y, h⟩ else x
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy
    have hyu : y ≠ u := fun h => hnadj (h ▸ hy.symm)
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
    have hφ : φ y = ⟨y, hyu⟩ := dif_pos hyu
    rw [hφ]
    exact hy
  · intro y₁ hy₁ y₂ hy₂ heq
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy₁ hy₂
    have hy₁u : y₁ ≠ u := fun h => hnadj (h ▸ hy₁.symm)
    have hy₂u : y₂ ≠ u := fun h => hnadj (h ▸ hy₂.symm)
    have hφ₁ : φ y₁ = ⟨y₁, hy₁u⟩ := dif_pos hy₁u
    have hφ₂ : φ y₂ = ⟨y₂, hy₂u⟩ := dif_pos hy₂u
    rw [hφ₁, hφ₂] at heq
    exact congrArg Subtype.val heq

lemma degree_le_induceNe_add_one (G : SimpleGraph V) [DecidableRel G.Adj] {u : V}
    (x : {z : V // z ≠ u}) :
    G.degree x.1 ≤ (induceNe G u).degree x + 1 := by
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  let φ : V → {z : V // z ≠ u} := fun y => if h : y ≠ u then ⟨y, h⟩ else x
  have herase_le : ((G.neighborFinset x.1).erase u).card ≤
      ((induceNe G u).neighborFinset x).card := by
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro y hy
      rw [Finset.mem_coe, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hy
      rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset]
      have hφ : φ y = ⟨y, hy.1⟩ := dif_pos hy.1
      rw [hφ]
      exact hy.2
    · intro y₁ hy₁ y₂ hy₂ heq
      rw [Finset.mem_coe, Finset.mem_erase] at hy₁ hy₂
      have hφ₁ : φ y₁ = ⟨y₁, hy₁.1⟩ := dif_pos hy₁.1
      have hφ₂ : φ y₂ = ⟨y₂, hy₂.1⟩ := dif_pos hy₂.1
      rw [hφ₁, hφ₂] at heq
      exact congrArg Subtype.val heq
  have hsub : G.neighborFinset x.1 ⊆ insert u ((G.neighborFinset x.1).erase u) := by
    intro y hy
    by_cases hyu : y = u
    · exact Finset.mem_insert.mpr (Or.inl hyu)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hyu, hy⟩))
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  omega

lemma degree_suppress_le_of_eq_left (G : SimpleGraph V) [DecidableRel G.Adj] {u v w : V}
    (huw : G.Adj u w) (hvw : v ≠ w) (hnadj : ¬ G.Adj v w)
    (x : {z : V // z ≠ u}) (hxv : x.1 = v) :
    G.degree x.1 ≤ (suppress G u v w).degree x := by
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  have hwu : w ≠ u := (G.ne_of_adj huw).symm
  let φ : V → {z : V // z ≠ u} := fun y => if h : y ≠ u then ⟨y, h⟩ else ⟨w, hwu⟩
  refine Finset.card_le_card_of_injOn φ ?_ ?_
  · intro y hy
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy ⊢
    by_cases hyu : y = u
    · subst hyu
      have hφ : φ y = ⟨w, hwu⟩ := dif_neg (not_not.mpr rfl)
      rw [hφ]
      exact ⟨fun h => hvw (hxv ▸ congrArg Subtype.val h), Or.inr (Or.inl ⟨hxv, rfl⟩)⟩
    · have hφ : φ y = ⟨y, hyu⟩ := dif_pos hyu
      rw [hφ]
      exact ⟨fun h => G.ne_of_adj hy (congrArg Subtype.val h), Or.inl hy⟩
  · intro y₁ hy₁ y₂ hy₂ heq
    rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset, hxv] at hy₁ hy₂
    by_cases h₁ : y₁ = u <;> by_cases h₂ : y₂ = u
    · rw [h₁, h₂]
    · have hφ₁ : φ y₁ = ⟨w, hwu⟩ := dif_neg (not_not.mpr h₁)
      have hφ₂ : φ y₂ = ⟨y₂, h₂⟩ := dif_pos h₂
      rw [hφ₁, hφ₂] at heq
      have hw_eq : w = y₂ := congrArg Subtype.val heq
      exact False.elim (hnadj (hw_eq ▸ hy₂))
    · have hφ₁ : φ y₁ = ⟨y₁, h₁⟩ := dif_pos h₁
      have hφ₂ : φ y₂ = ⟨w, hwu⟩ := dif_neg (not_not.mpr h₂)
      rw [hφ₁, hφ₂] at heq
      have hw_eq : y₁ = w := congrArg Subtype.val heq
      exact False.elim (hnadj (hw_eq ▸ hy₁))
    · have hφ₁ : φ y₁ = ⟨y₁, h₁⟩ := dif_pos h₁
      have hφ₂ : φ y₂ = ⟨y₂, h₂⟩ := dif_pos h₂
      rw [hφ₁, hφ₂] at heq
      exact congrArg Subtype.val heq

lemma degree_suppress_comm (G : SimpleGraph V) [DecidableRel G.Adj] (u v w : V)
    (x : {z : V // z ≠ u}) :
    (suppress G u v w).degree x = (suppress G u w v).degree x := by
  simp only [← SimpleGraph.card_neighborFinset_eq_degree]
  congr 1
  ext y
  rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
  dsimp [suppress]
  tauto

lemma degree_suppress_le (G : SimpleGraph V) [DecidableRel G.Adj] {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : v ≠ w) (hnadj : ¬ G.Adj v w)
    (x : {z : V // z ≠ u}) (hx : x.1 = v ∨ x.1 = w ∨ ¬ G.Adj u x.1) :
    G.degree x.1 ≤ (suppress G u v w).degree x := by
  rcases hx with hxv | hxw | hnadj_ux
  · exact degree_suppress_le_of_eq_left G huw hvw hnadj x hxv
  · rw [degree_suppress_comm G u v w x]
    exact degree_suppress_le_of_eq_left G huv hvw.symm (fun h => hnadj h.symm) x hxw
  · simp only [← SimpleGraph.card_neighborFinset_eq_degree]
    let φ : V → {z : V // z ≠ u} := fun y => if h : y ≠ u then ⟨y, h⟩ else x
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro y hy
      rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy ⊢
      have hyu : y ≠ u := fun h => hnadj_ux (h ▸ hy.symm)
      have hφ : φ y = ⟨y, hyu⟩ := dif_pos hyu
      rw [hφ]
      exact ⟨fun h => G.ne_of_adj hy (congrArg Subtype.val h), Or.inl hy⟩
    · intro y₁ hy₁ y₂ hy₂ heq
      rw [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hy₁ hy₂
      have hy₁u : y₁ ≠ u := fun h => hnadj_ux (h ▸ hy₁.symm)
      have hy₂u : y₂ ≠ u := fun h => hnadj_ux (h ▸ hy₂.symm)
      have hφ₁ : φ y₁ = ⟨y₁, hy₁u⟩ := dif_pos hy₁u
      have hφ₂ : φ y₂ = ⟨y₂, hy₂u⟩ := dif_pos hy₂u
      rw [hφ₁, hφ₂] at heq
      exact congrArg Subtype.val heq

/-! ### Part 3: Neighbor Extraction and Main Induction -/

lemma card_subtype_ne {W : Type*} [Fintype W] [DecidableEq W] (u : W) :
    Fintype.card {x : W // x ≠ u} = Fintype.card W - 1 := by
  have huniq : Unique {x : W // x = u} := ⟨⟨⟨u, rfl⟩⟩, fun ⟨x, hx⟩ => Subtype.ext hx⟩
  rw [Fintype.card_subtype_compl, @Fintype.card_unique {x : W // x = u} huniq _]

lemma card_ge_four_of_deg_ge_three {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {r : W}
    (hW : 2 ≤ Fintype.card W) (hdeg : ∀ x : W, x ≠ r → 3 ≤ G.degree x) :
    4 ≤ Fintype.card W := by
  have h1 : 1 < Fintype.card W := by omega
  obtain ⟨x, hxr⟩ := Fintype.exists_ne_of_one_lt_card h1 r
  have hx3 : 3 ≤ G.degree x := hdeg x hxr
  have hlt : G.degree x < Fintype.card W := G.degree_lt_card_verts x
  omega

lemma exists_adj_of_degree_pos {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (u : W)
    (hpos : 1 ≤ G.degree u) :
    ∃ v : W, G.Adj u v := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hpos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset u).card)
  exact ⟨v, (G.mem_neighborFinset u v).mp hv⟩

lemma degree_le_one_neighbors {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {u : W}
    (hdeg : G.degree u ≤ 1) (hW : 2 ≤ Fintype.card W) :
    ∃ r' : {z : W // z ≠ u}, ∀ x : {z : W // z ≠ u}, x ≠ r' → ¬ G.Adj u x.1 := by
  by_cases h0 : G.degree u = 0
  · have h1 : 1 < Fintype.card W := by omega
    obtain ⟨d, hdu⟩ := Fintype.exists_ne_of_one_lt_card h1 u
    refine ⟨⟨d, hdu⟩, fun x _ hadj => ?_⟩
    have hmem : x.1 ∈ G.neighborFinset u := (G.mem_neighborFinset u x.1).mpr hadj
    have hpos : 0 < G.degree u := by
      rw [← SimpleGraph.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨x.1, hmem⟩
    omega
  · obtain ⟨v, huv⟩ := exists_adj_of_degree_pos G u (by omega)
    have hvu : v ≠ u := (G.ne_of_adj huv).symm
    refine ⟨⟨v, hvu⟩, fun x hxr' hadj => ?_⟩
    rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
    have hxv : x.1 = v := Finset.card_le_one.mp hdeg
      x.1 ((G.mem_neighborFinset u x.1).mpr hadj)
      v ((G.mem_neighborFinset u v).mpr huv)
    exact hxr' (Subtype.ext hxv)

lemma degree_eq_two_other_neighbor {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {u v : W}
    (hdeg : G.degree u = 2) (huv : G.Adj u v) :
    ∃ w : W, v ≠ w ∧ G.Adj u w ∧ ∀ x : W, G.Adj u x → x = v ∨ x = w := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
  have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr huv
  have hcard_er : ((G.neighborFinset u).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hv_mem, hdeg]
  obtain ⟨w, hw_eq⟩ := Finset.card_eq_one.mp hcard_er
  have hw_er : w ∈ (G.neighborFinset u).erase v := by
    rw [hw_eq]; exact Finset.mem_singleton_self w
  have hwv : w ≠ v := (Finset.mem_erase.mp hw_er).1
  have huw : G.Adj u w := (G.mem_neighborFinset u w).mp (Finset.mem_erase.mp hw_er).2
  refine ⟨w, hwv.symm, huw, fun x hadj => ?_⟩
  by_cases hxv : x = v
  · exact Or.inl hxv
  · have hx_er : x ∈ (G.neighborFinset u).erase v :=
      Finset.mem_erase.mpr ⟨hxv, (G.mem_neighborFinset u x).mpr hadj⟩
    rw [hw_eq, Finset.mem_singleton] at hx_er
    exact Or.inr hx_er

lemma degree_eq_two_neighbors {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {u : W}
    (hdeg : G.degree u = 2) :
    ∃ v w : W, v ≠ w ∧ G.Adj u v ∧ G.Adj u w ∧ ∀ x : W, G.Adj u x → x = v ∨ x = w := by
  obtain ⟨v, huv⟩ := exists_adj_of_degree_pos G u (by omega)
  obtain ⟨w, hvw, huw, hall⟩ := degree_eq_two_other_neighbor G hdeg huv
  exact ⟨v, w, hvw, huv, huw, hall⟩

lemma degree_eq_three_clique_or_nonadj {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] {u : W}
    (hdeg : G.degree u = 3) :
    ContainsK4Homeomorph G ∨
      ∃ v w c : W, v ≠ w ∧ v ≠ c ∧ w ≠ c ∧
        G.Adj u v ∧ G.Adj u w ∧ G.Adj u c ∧ ¬ G.Adj v w ∧
        ∀ x : W, G.Adj u x → x = v ∨ x = w ∨ x = c := by
  obtain ⟨v, huv⟩ := exists_adj_of_degree_pos G u (by omega)
  rw [← SimpleGraph.card_neighborFinset_eq_degree] at hdeg
  have hv_mem : v ∈ G.neighborFinset u := (G.mem_neighborFinset u v).mpr huv
  have hcard_er1 : ((G.neighborFinset u).erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hv_mem, hdeg]
  obtain ⟨w, hw_er1⟩ := Finset.card_pos.mp (by omega : 0 < ((G.neighborFinset u).erase v).card)
  have hwv : w ≠ v := (Finset.mem_erase.mp hw_er1).1
  have huw : G.Adj u w := (G.mem_neighborFinset u w).mp (Finset.mem_erase.mp hw_er1).2
  have hcard_er2 : (((G.neighborFinset u).erase v).erase w).card = 1 := by
    rw [Finset.card_erase_of_mem hw_er1, hcard_er1]
  obtain ⟨c, hc_eq⟩ := Finset.card_eq_one.mp hcard_er2
  have hc_er2 : c ∈ ((G.neighborFinset u).erase v).erase w := by
    rw [hc_eq]; exact Finset.mem_singleton_self c
  have hcw : c ≠ w := (Finset.mem_erase.mp hc_er2).1
  have hc_er1 : c ∈ (G.neighborFinset u).erase v := (Finset.mem_erase.mp hc_er2).2
  have hcv : c ≠ v := (Finset.mem_erase.mp hc_er1).1
  have huc : G.Adj u c := (G.mem_neighborFinset u c).mp (Finset.mem_erase.mp hc_er1).2
  have hall : ∀ x : W, G.Adj u x → x = v ∨ x = w ∨ x = c := by
    intro x hadj
    by_cases hxv : x = v
    · exact Or.inl hxv
    · by_cases hxw : x = w
      · exact Or.inr (Or.inl hxw)
      · have hx_er2 : x ∈ ((G.neighborFinset u).erase v).erase w :=
          Finset.mem_erase.mpr ⟨hxw, Finset.mem_erase.mpr ⟨hxv, (G.mem_neighborFinset u x).mpr hadj⟩⟩
        rw [hc_eq, Finset.mem_singleton] at hx_er2
        exact Or.inr (Or.inr hx_er2)
  by_cases hvw : G.Adj v w
  · by_cases hvc : G.Adj v c
    · by_cases hwc : G.Adj w c
      · exact Or.inl (containsK4Homeomorph_of_clique4 huv huw huc hvw hvc hwc)
      · refine Or.inr ⟨w, c, v, hcw.symm, hwv, hcv, huw, huc, huv, hwc, ?_⟩
        intro x hx; rcases hall x hx with rfl | rfl | rfl <;> tauto
    · refine Or.inr ⟨v, c, w, hcv.symm, hwv.symm, hcw, huv, huc, huw, hvc, ?_⟩
      intro x hx; rcases hall x hx with rfl | rfl | rfl <;> tauto
  · exact Or.inr ⟨v, w, c, hwv.symm, hcv.symm, hcw.symm, huv, huw, huc, hvw, hall⟩

lemma not_isSeriesParallel_of_deg_ge_three_except_one_aux :
    ∀ (n : ℕ),
      ∀ {W : Type*} [Fintype W] [DecidableEq W]
        (G : SimpleGraph W) [DecidableRel G.Adj] (r : W),
        Fintype.card W ≤ n →
        2 ≤ Fintype.card W →
        (∀ x : W, x ≠ r → 3 ≤ G.degree x) →
        ¬ IsSeriesParallel G := by
  intro n
  induction n with
  | zero =>
    intro W _ _ G _ r hn hW _
    omega
  | succ n' ih_n =>
    intro W _ _ G _ r hn hW hdeg
    suffices h_inner : ∀ (e : ℕ) (G : SimpleGraph W) [DecidableRel G.Adj] (r : W),
        G.edgeFinset.card ≤ e →
        (∀ x : W, x ≠ r → 3 ≤ G.degree x) →
        ¬ IsSeriesParallel G by
      exact h_inner G.edgeFinset.card G r le_rfl hdeg
    intro e
    induction e with
    | zero =>
      intro G _ r he hdeg_G hSP
      have h4 : 4 ≤ Fintype.card W := card_ge_four_of_deg_ge_three G hW hdeg_G
      have h1 : 1 < Fintype.card W := by omega
      obtain ⟨x, hxr⟩ := Fintype.exists_ne_of_one_lt_card h1 r
      have hx3 : 3 ≤ G.degree x := hdeg_G x hxr
      obtain ⟨y, hxy⟩ := exists_adj_of_degree_pos G x (by omega)
      have hmem : s(x, y) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr hxy
      have hpos : 0 < G.edgeFinset.card := Finset.card_pos.mpr ⟨s(x, y), hmem⟩
      omega
    | succ e' ih_e =>
      intro G _ r he hdeg_G hSP
      have h4 : 4 ≤ Fintype.card W := card_ge_four_of_deg_ge_three G hW hdeg_G
      by_cases h_le1 : G.degree r ≤ 1
      · obtain ⟨r', hr'⟩ := degree_le_one_neighbors G h_le1 hW
        let G' := induceNe G r
        have hSP' : IsSeriesParallel G' := isSeriesParallel_induceNe r hSP
        have hcard_lt : Fintype.card {x : W // x ≠ r} ≤ n' := by
          rw [card_subtype_ne]; omega
        have hcard_ge2 : 2 ≤ Fintype.card {x : W // x ≠ r} := by
          rw [card_subtype_ne]; omega
        have hdeg' : ∀ x : {x : W // x ≠ r}, x ≠ r' → 3 ≤ G'.degree x := by
          intro x hxr'
          exact (hdeg_G x.1 x.2).trans (degree_induceNe_le_of_not_adj G x (hr' x hxr'))
        exact ih_n G' r' hcard_lt hcard_ge2 hdeg' hSP'
      · by_cases h_eq2 : G.degree r = 2
        · obtain ⟨v, w, hvw, hrv, hrw, hall_r⟩ := degree_eq_two_neighbors G h_eq2
          have hvr : v ≠ r := (G.ne_of_adj hrv).symm
          have hwr : w ≠ r := (G.ne_of_adj hrw).symm
          by_cases hadj_vw : G.Adj v w
          · let G₁ := induceNe G r
            have hSP₁ : IsSeriesParallel G₁ := isSeriesParallel_induceNe r hSP
            let v₁ : {x : W // x ≠ r} := ⟨v, hvr⟩
            let w₁ : {x : W // x ≠ r} := ⟨w, hwr⟩
            have hv₁w₁ : v₁ ≠ w₁ := fun h => hvw (congrArg Subtype.val h)
            have hadj₁_vw : G₁.Adj v₁ w₁ := hadj_vw
            have hcard₁_le : Fintype.card {x : W // x ≠ r} ≤ n' := by
              rw [card_subtype_ne]; omega
            have hcard₁_ge3 : 3 ≤ Fintype.card {x : W // x ≠ r} := by
              rw [card_subtype_ne]; omega
            have hdeg₁_other : ∀ x : {x : W // x ≠ r}, x ≠ v₁ → x ≠ w₁ → 3 ≤ G₁.degree x := by
              intro x hxv₁ hxw₁
              have hnadj_rx : ¬ G.Adj r x.1 := by
                intro hrx
                rcases hall_r x.1 hrx with h1 | h2
                · exact hxv₁ (Subtype.ext h1)
                · exact hxw₁ (Subtype.ext h2)
              exact (hdeg_G x.1 x.2).trans (degree_induceNe_le_of_not_adj G x hnadj_rx)
            have hdeg₁_v₁ : 2 ≤ G₁.degree v₁ := by
              have h1 : 3 ≤ G.degree v₁.1 := hdeg_G v hvr
              have h2 : G.degree v₁.1 ≤ G₁.degree v₁ + 1 := degree_le_induceNe_add_one G v₁
              omega
            have hdeg₁_w₁ : 2 ≤ G₁.degree w₁ := by
              have h1 : 3 ≤ G.degree w₁.1 := hdeg_G w hwr
              have h2 : G.degree w₁.1 ≤ G₁.degree w₁ + 1 := degree_le_induceNe_add_one G w₁
              omega
            by_cases h3_w₁ : 3 ≤ G₁.degree w₁
            · have hdeg₁ : ∀ x : {x : W // x ≠ r}, x ≠ v₁ → 3 ≤ G₁.degree x := by
                intro x hxv₁
                by_cases hxw₁ : x = w₁
                · exact hxw₁ ▸ h3_w₁
                · exact hdeg₁_other x hxv₁ hxw₁
              exact ih_n G₁ v₁ hcard₁_le (by omega) hdeg₁ hSP₁
            · by_cases h3_v₁ : 3 ≤ G₁.degree v₁
              · have hdeg₁ : ∀ x : {x : W // x ≠ r}, x ≠ w₁ → 3 ≤ G₁.degree x := by
                  intro x hxw₁
                  by_cases hxv₁ : x = v₁
                  · exact hxv₁ ▸ h3_v₁
                  · exact hdeg₁_other x hxv₁ hxw₁
                exact ih_n G₁ w₁ hcard₁_le (by omega) hdeg₁ hSP₁
              · have heq2_v₁ : G₁.degree v₁ = 2 := by omega
                have heq2_w₁ : G₁.degree w₁ = 2 := by omega
                obtain ⟨w', hv₁w', hw₁w', hall_w₁⟩ :=
                  degree_eq_two_other_neighbor G₁ heq2_w₁ hadj₁_vw.symm
                have hw₁_ne_w' : w₁ ≠ w' := G₁.ne_of_adj hw₁w'
                by_cases hadj₁_vw' : G₁.Adj v₁ w'
                · have hall_v₁ : ∀ x, G₁.Adj v₁ x → x = w₁ ∨ x = w' := by
                    obtain ⟨z, hw₁z, hv₁z, hall_v₁'⟩ :=
                      degree_eq_two_other_neighbor G₁ heq2_v₁ hadj₁_vw
                    rcases hall_v₁' w' hadj₁_vw' with h1 | rfl
                    · exact False.elim (hw₁_ne_w' h1.symm)
                    · exact hall_v₁'
                  have hdeg₁_w' : 3 ≤ G₁.degree w' :=
                    hdeg₁_other w' hv₁w'.symm hw₁_ne_w'.symm
                  have hcard₁_ge4 : 4 ≤ Fintype.card {x : W // x ≠ r} := by
                    have hlt : G₁.degree w' < Fintype.card {x : W // x ≠ r} :=
                      G₁.degree_lt_card_verts w'
                    omega
                  let G₂ := induceNe G₁ w₁
                  have hSP₂ : IsSeriesParallel G₂ := isSeriesParallel_induceNe w₁ hSP₁
                  let v₂ : {x // x ≠ w₁} := ⟨v₁, hv₁w₁⟩
                  let w'₂ : {x // x ≠ w₁} := ⟨w', hw₁_ne_w'.symm⟩
                  have hv₂w'₂ : v₂ ≠ w'₂ := fun h => hv₁w' (congrArg Subtype.val h)
                  let G₃ := induceNe G₂ v₂
                  have hSP₃ : IsSeriesParallel G₃ := isSeriesParallel_induceNe v₂ hSP₂
                  let w'₃ : {x // x ≠ v₂} := ⟨w'₂, hv₂w'₂.symm⟩
                  have hcard₂ : Fintype.card {x // x ≠ w₁} = Fintype.card {x : W // x ≠ r} - 1 :=
                    card_subtype_ne w₁
                  have hcard₃ : Fintype.card {x // x ≠ v₂} = Fintype.card {x // x ≠ w₁} - 1 :=
                    card_subtype_ne v₂
                  have hdeg₃ : ∀ x : {x // x ≠ v₂}, x ≠ w'₃ → 3 ≤ G₃.degree x := by
                    intro x hxw'₃
                    have hx_ne_w' : x.1.1 ≠ w' := fun h =>
                      hxw'₃ (Subtype.ext (Subtype.ext h))
                    have hx_ne_v₁ : x.1.1 ≠ v₁ := fun h =>
                      x.2 (Subtype.ext h)
                    have hx_ne_w₁ : x.1.1 ≠ w₁ := x.1.2
                    have hnadj_w₁ : ¬ G₁.Adj w₁ x.1.1 := by
                      intro h
                      rcases hall_w₁ x.1.1 h with h1 | h2
                      · exact hx_ne_v₁ h1
                      · exact hx_ne_w' h2
                    have hnadj_v₂ : ¬ G₂.Adj v₂ x.1 := by
                      intro h
                      rcases hall_v₁ x.1.1 h with h1 | h2
                      · exact hx_ne_w₁ h1
                      · exact hx_ne_w' h2
                    have hle1 : 3 ≤ G₁.degree x.1.1 := hdeg₁_other x.1.1 hx_ne_v₁ hx_ne_w₁
                    have hle2 : G₁.degree x.1.1 ≤ G₂.degree x.1 :=
                      degree_induceNe_le_of_not_adj G₁ x.1 hnadj_w₁
                    have hle3 : G₂.degree x.1 ≤ G₃.degree x :=
                      degree_induceNe_le_of_not_adj G₂ x hnadj_v₂
                    exact hle1.trans (hle2.trans hle3)
                  exact ih_n G₃ w'₃ (by omega) (by omega) hdeg₃ hSP₃
                · let G₂ := suppress G₁ w₁ v₁ w'
                  have hSP₂ : IsSeriesParallel G₂ :=
                    isSeriesParallel_suppress hadj₁_vw.symm hw₁w' hSP₁
                  let v₂ : {x // x ≠ w₁} := ⟨v₁, hv₁w₁⟩
                  have hcard₂ : Fintype.card {x // x ≠ w₁} = Fintype.card {x : W // x ≠ r} - 1 :=
                    card_subtype_ne w₁
                  have hdeg₂ : ∀ x : {x // x ≠ w₁}, x ≠ v₂ → 3 ≤ G₂.degree x := by
                    intro x hxv₂
                    have hx_ne_v₁ : x.1 ≠ v₁ := fun h => hxv₂ (Subtype.ext h)
                    have hx_cases : x.1 = v₁ ∨ x.1 = w' ∨ ¬ G₁.Adj w₁ x.1 := by
                      by_cases h : G₁.Adj w₁ x.1
                      · rcases hall_w₁ x.1 h with h1 | h2
                        · exact Or.inl h1
                        · exact Or.inr (Or.inl h2)
                      · exact Or.inr (Or.inr h)
                    exact (hdeg₁_other x.1 hx_ne_v₁ x.2).trans
                      (degree_suppress_le G₁ hadj₁_vw.symm hw₁w' hv₁w' hadj₁_vw' x hx_cases)
                  exact ih_n G₂ v₂ (by omega) (by omega) hdeg₂ hSP₂
          · let G' := suppress G r v w
            have hSP' : IsSeriesParallel G' := isSeriesParallel_suppress hrv hrw hSP
            let v' : {x : W // x ≠ r} := ⟨v, hvr⟩
            have hcard_lt : Fintype.card {x : W // x ≠ r} ≤ n' := by
              rw [card_subtype_ne]; omega
            have hcard_ge2 : 2 ≤ Fintype.card {x : W // x ≠ r} := by
              rw [card_subtype_ne]; omega
            have hdeg' : ∀ x : {x : W // x ≠ r}, x ≠ v' → 3 ≤ G'.degree x := by
              intro x _
              have hx_cases : x.1 = v ∨ x.1 = w ∨ ¬ G.Adj r x.1 := by
                by_cases h : G.Adj r x.1
                · rcases hall_r x.1 h with h1 | h2
                  · exact Or.inl h1
                  · exact Or.inr (Or.inl h2)
                · exact Or.inr (Or.inr h)
              exact (hdeg_G x.1 x.2).trans (degree_suppress_le G hrv hrw hvw hadj_vw x hx_cases)
            exact ih_n G' v' hcard_lt hcard_ge2 hdeg' hSP'
        · by_cases h_eq3 : G.degree r = 3
          · rcases degree_eq_three_clique_or_nonadj G h_eq3 with hK4 |
              ⟨v, w, c, hvw, hvc, hwc, hrv, hrw, hrc, hnadj_vw, hall_r⟩
            · exact hSP hK4
            · let G' := suppress G r v w
              have hSP' : IsSeriesParallel G' := isSeriesParallel_suppress hrv hrw hSP
              have hcr : c ≠ r := (G.ne_of_adj hrc).symm
              let c' : {x : W // x ≠ r} := ⟨c, hcr⟩
              have hcard_lt : Fintype.card {x : W // x ≠ r} ≤ n' := by
                rw [card_subtype_ne]; omega
              have hcard_ge2 : 2 ≤ Fintype.card {x : W // x ≠ r} := by
                rw [card_subtype_ne]; omega
              have hdeg' : ∀ x : {x : W // x ≠ r}, x ≠ c' → 3 ≤ G'.degree x := by
                intro x hxc'
                have hx_ne_c : x.1 ≠ c := fun h => hxc' (Subtype.ext h)
                have hx_cases : x.1 = v ∨ x.1 = w ∨ ¬ G.Adj r x.1 := by
                  by_cases h : G.Adj r x.1
                  · rcases hall_r x.1 h with h1 | h2 | h3
                    · exact Or.inl h1
                    · exact Or.inr (Or.inl h2)
                    · exact False.elim (hx_ne_c h3)
                  · exact Or.inr (Or.inr h)
                exact (hdeg_G x.1 x.2).trans (degree_suppress_le G hrv hrw hvw hnadj_vw x hx_cases)
              exact ih_n G' c' hcard_lt hcard_ge2 hdeg' hSP'
          · have h_ge4 : 4 ≤ G.degree r := by omega
            obtain ⟨u, hru⟩ := exists_adj_of_degree_pos G r (by omega)
            let G' := G.deleteEdges {s(r, u)}
            have hSP' : IsSeriesParallel G' :=
              isSeriesParallel_mono (SimpleGraph.deleteEdges_le _) hSP
            have he' : G'.edgeFinset.card ≤ e' := by
              have hlt : G'.edgeFinset.card < G.edgeFinset.card :=
                card_edgeFinset_deleteEdges_lt G hru
              omega
            have hdeg' : ∀ x : W, x ≠ u → 3 ≤ G'.degree x := by
              intro x hxu
              by_cases hxr : x = r
              · subst hxr
                have hle : G.degree x ≤ G'.degree x + 1 :=
                  degree_le_deleteEdges_add_one G x u
                omega
              · exact (hdeg_G x hxr).trans (degree_deleteEdges_le_of_ne G hxr hxu)
            exact ih_e G' u he' hdeg' hSP'

end SolChvatalDirac

open ChvatalPolytopes.SeriesParallel (IsSeriesParallel)
open SolChvatalDirac

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G)
    (hV : 2 ≤ Fintype.card V) :
    ∃ a b : V, a ≠ b ∧ G.degree a ≤ 2 ∧ G.degree b ≤ 2 := by
  by_contra h
  simp only [not_exists, not_and, not_le] at h
  by_cases hex : ∃ r : V, G.degree r ≤ 2
  · rcases hex with ⟨r, hr⟩
    have hdeg : ∀ x : V, x ≠ r → 3 ≤ G.degree x := by
      intro x hxr
      have := h r x (Ne.symm hxr) hr
      omega
    exact not_isSeriesParallel_of_deg_ge_three_except_one_aux
      (Fintype.card V) G r le_rfl hV hdeg hG
  · simp only [not_exists, not_le] at hex
    obtain ⟨r⟩ := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card V)
    have hdeg : ∀ x : V, x ≠ r → 3 ≤ G.degree x := fun x _ => hex x
    exact not_isSeriesParallel_of_deg_ge_three_except_one_aux
      (Fintype.card V) G r le_rfl hV hdeg hG
