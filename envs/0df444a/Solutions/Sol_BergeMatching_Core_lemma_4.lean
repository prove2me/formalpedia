-- Prove2me | solution 1 for BergeMatching.Core.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:02:57.747881+00:00
-- url     : https://prove2.me/submissions/66f6017c-935a-4d8c-ab2e-ccef464d5e20

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain
import Definitions.Def_BergeMatching_Core_Arrows



namespace BergeMatching.Core

open SimpleGraph
set_option linter.unusedSectionVars false
set_option linter.deprecated false

section Base
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {M : G.Subgraph}

lemma bm_alt_prefix {a b c : Option V} {p : (barGraph G M).Walk a b}
    {q : (barGraph G M).Walk b c}
    (h : IsAlternatingWrt (barStrong M) (p.append q)) : IsAlternatingWrt (barStrong M) p := by
  refine ⟨h.1.of_append_left, ?_⟩
  have := h.2
  rw [Walk.edges_append] at this
  exact this.left_of_append

lemma bm_alt_takeUntil {a b : Option V} (u : Option V) {p : (barGraph G M).Walk a b}
    (hu : u ∈ p.support) (h : IsAlternatingWrt (barStrong M) p) :
    IsAlternatingWrt (barStrong M) (p.takeUntil u hu) := by
  rw [← p.take_spec hu] at h
  exact bm_alt_prefix h

lemma bm_len_ne_zero {x : V} (q : (barGraph G M).Walk none (some x)) : q.length ≠ 0 := by
  intro h
  have := Walk.eq_of_length_eq_zero h
  simp at this

lemma bm_alt_concat {a b c : Option V} {p : (barGraph G M).Walk a b}
    (hp : IsAlternatingWrt (barStrong M) p)
    (hnil : ¬ p.Nil) (hadj : (barGraph G M).Adj b c) (hne : s(b, c) ∉ p.edges)
    (halt : s(p.penultimate, b) ∈ barStrong M ↔ s(b, c) ∉ barStrong M) :
    IsAlternatingWrt (barStrong M) (p.concat hadj) := by
  refine ⟨?_, ?_⟩
  · rw [Walk.isTrail_def, Walk.edges_concat, List.concat_eq_append, List.nodup_append]
    refine ⟨hp.1.edges_nodup, List.nodup_singleton _, ?_⟩
    intro x hx y hy
    simp at hy
    subst hy
    rintro rfl
    exact hne hx
  · rw [Walk.edges_concat, List.concat_eq_append]
    refine hp.2.append (List.isChain_singleton _) ?_
    intro x hx y hy
    have hne' : p.edges ≠ [] := Walk.edges_eq_nil.not.mpr hnil
    rw [List.getLast?_eq_getLast hne'] at hx
    simp only [Option.mem_def, Option.some.injEq] at hx
    rw [Walk.getLast_edges_eq_mk_penultimate_end] at hx
    simp at hy
    subst hx hy
    exact halt

lemma bm_strong_some (x y : V) : s(some x, some y) ∈ barStrong M ↔ s(x, y) ∈ M.edgeSet := by
  constructor
  · rintro (⟨e, he, hee⟩ | ⟨n, -, hn⟩)
    · rw [← Sym2.map_pair_eq] at hee
      rwa [← Sym2.map.injective (Option.some_injective V) hee]
    · simp at hn
  · intro h; left; exact ⟨_, h, Sym2.map_pair_eq _ _ _⟩

lemma bm_strong_none (x : V) : s(none, some x) ∈ barStrong M ↔ IsNeutral M x := by
  constructor
  · rintro (⟨e, he, hee⟩ | ⟨n, hn, he⟩)
    · induction e using Sym2.ind
      simp at hee
    · simp at he
      rw [he]; exact hn
  · intro h; right; exact ⟨x, h, rfl⟩

lemma bm_mate_unique (hM : M.IsMatching) {x y y' : V} (h : M.Adj x y) (h' : M.Adj x y') :
    y = y' :=
  (hM (M.edge_vert h)).unique h h'

lemma bm_exists_mate {x : V} (hx : ¬ IsNeutral M x) : ∃ y, M.Adj x y := by
  unfold IsNeutral at hx
  push_neg at hx
  obtain ⟨e, he, hxe⟩ := hx
  induction e using Sym2.ind with
  | h a b =>
    rw [Subgraph.mem_edgeSet] at he
    rcases Sym2.mem_iff.mp hxe with rfl | rfl
    · exact ⟨b, he⟩
    · exact ⟨a, he.symm⟩

lemma bm_neutral_not_adj {n x : V} (hn : IsNeutral M n) : ¬ M.Adj n x := by
  intro h
  exact hn _ (Subgraph.mem_edgeSet.mpr h) (Sym2.mem_mk_left _ _)

lemma bm_strong_nonneutral (hM : M.IsMatching) {z : Option V} {x : V} (hx : ¬ IsNeutral M x)
    (h : s(z, some x) ∈ barStrong M) : ∃ y, z = some y ∧ M.Adj x y := by
  cases z with
  | none => exact absurd ((bm_strong_none x).mp h) hx
  | some y =>
    refine ⟨y, rfl, ?_⟩
    rw [bm_strong_some, Subgraph.mem_edgeSet] at h
    exact h.symm

lemma bm_arrow_of_mem_support {b : Option V} {p : (barGraph G M).Walk none b}
    (hp : IsAlternatingWrt (barStrong M) p) {x : V} (hx : some x ∈ p.support) :
    ∃ z, Arrow G M z (some x) :=
  ⟨_, p.takeUntil _ hx, bm_alt_takeUntil _ hx hp, bm_len_ne_zero _, rfl⟩

lemma bm_arrow_into_of_arrow_from {x : V} {y : Option V} (h : Arrow G M (some x) y) :
    ∃ z, Arrow G M z (some x) := by
  obtain ⟨p, hp, hl, hpen⟩ := h
  have hnil : ¬ p.Nil := by rw [Walk.nil_iff_length_eq]; exact hl
  have := p.fst_mem_support_of_mem_edges (p.mk_penultimate_end_mem_edges hnil)
  rw [hpen] at this
  exact bm_arrow_of_mem_support hp this

lemma bm_arrow_neutral {n x : V} (hn : IsNeutral M n) (hadj : G.Adj n x) :
    Arrow G M (some n) (some x) := by
  refine ⟨Walk.cons (show (barGraph G M).Adj none (some n) from hn)
    (Walk.cons (show (barGraph G M).Adj (some n) (some x) from hadj) Walk.nil), ⟨?_, ?_⟩,
    by simp, rfl⟩
  · rw [Walk.isTrail_def]; simp
  · have h1 : s(none, some n) ∈ barStrong M := (bm_strong_none n).mpr hn
    have h2 : s(some n, some x) ∉ barStrong M := by
      rw [bm_strong_some, Subgraph.mem_edgeSet]; exact bm_neutral_not_adj hn
    simp [h1, h2]

lemma bm_extend (hM : M.IsMatching) {z : Option V} {x : V} (h : Arrow G M z (some x))
    {c : Option V} (hadj : (barGraph G M).Adj (some x) c)
    (hc : ∀ p : (barGraph G M).Walk none (some x), IsAlternatingWrt (barStrong M) p →
      s(some x, c) ∉ p.edges)
    (halt : s(z, some x) ∈ barStrong M ↔ s(some x, c) ∉ barStrong M) :
    Arrow G M (some x) c := by
  obtain ⟨p, hp, hl, hpen⟩ := h
  have hnil : ¬ p.Nil := by rw [Walk.nil_iff_length_eq]; exact hl
  refine ⟨p.concat hadj, bm_alt_concat hp hnil hadj (hc p hp) (by rw [hpen]; exact halt),
    by simp, by simp [Walk.penultimate_concat]⟩

/-- first visit lemma -/
lemma bm_first_visit (T : Set V) (hT : ∃ t ∈ T, ∃ z, Arrow G M z (some t)) :
    ∃ t ∈ T, ∃ Q : (barGraph G M).Walk none (some t), IsAlternatingWrt (barStrong M) Q ∧
      ∀ t' ∈ T, some t' ∈ Q.support → t' = t := by
  classical
  have hex : ∃ n, ∃ t ∈ T, ∃ Q : (barGraph G M).Walk none (some t),
      IsAlternatingWrt (barStrong M) Q ∧ Q.length = n := by
    obtain ⟨t, ht, z, Q, hQ, hl, -⟩ := hT
    exact ⟨_, t, ht, Q, hQ, rfl⟩
  obtain ⟨t, ht, Q, hQ, hn⟩ := Nat.find_spec hex
  refine ⟨t, ht, Q, hQ, ?_⟩
  intro t' ht' hmem
  by_contra hne
  have hlt := Walk.length_takeUntil_lt_length hmem (by simpa using hne)
  have := Nat.find_min hex (hn ▸ hlt)
  exact this ⟨t', ht', Q.takeUntil _ hmem, bm_alt_takeUntil _ hmem hQ, rfl⟩

end Base
section L4
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {M : G.Subgraph}

lemma bm_inacc_not_mem {z : V} (hz : IsInaccessible G M z) {b : Option V}
    (p : (barGraph G M).Walk none b) (hp : IsAlternatingWrt (barStrong M) p) :
    some z ∉ p.support := by
  intro h
  obtain ⟨y, hy⟩ := bm_arrow_of_mem_support hp h
  exact (hz.2 y).1 hy

lemma bm_inacc_edge_not_mem {z : V} (hz : IsInaccessible G M z) {b : Option V} (c : Option V)
    (p : (barGraph G M).Walk none b) (hp : IsAlternatingWrt (barStrong M) p) :
    s(c, some z) ∉ p.edges := fun h =>
  bm_inacc_not_mem hz p hp (p.snd_mem_support_of_mem_edges h)

lemma bm_has_arrow {x : V} (hx : ¬ IsNeutral M x) (hI : ¬ IsInaccessible G M x) :
    ∃ z, Arrow G M z (some x) := by
  unfold IsInaccessible at hI
  push_neg at hI
  obtain ⟨y, hy⟩ := hI hx
  by_cases h : Arrow G M y (some x)
  · exact ⟨y, h⟩
  · exact bm_arrow_into_of_arrow_from (hy h)

/-- core of lemma 4, for a single edge -/
lemma bm_l4_edge (hM : M.IsMatching) {z w : V} (hz : IsInaccessible G M z)
    (hw : ¬ IsInaccessible G M w) (hadj : G.Adj z w) :
    s(z, w) ∉ M.edgeSet ∧ ¬ Arrow G M (some z) (some w) ∧ ¬ Arrow G M (some w) (some z) ∧
      IsWeakPt G M w := by
  have hwn : ¬ IsNeutral M w := by
    intro hn
    exact (hz.2 (some w)).1 (bm_arrow_neutral hn hadj.symm)
  have hno : ∀ p : (barGraph G M).Walk none (some w), IsAlternatingWrt (barStrong M) p →
      s(some w, some z) ∉ p.edges := by
    intro p hp h
    rw [Sym2.eq_swap] at h
    exact bm_inacc_edge_not_mem hz _ p hp (by rwa [Sym2.eq_swap])
  -- any arrow into w is weak
  have hweak : ∀ u, Arrow G M u (some w) → s(u, some w) ∉ barStrong M := by
    intro u hu hs
    have hzw : ¬ M.Adj w z := by
      intro hm
      obtain ⟨y, rfl, hy⟩ := bm_strong_nonneutral hM hwn hs
      have := bm_mate_unique hM hy hm
      subst this
      exact (hz.2 (some w)).2 hu
    apply (hz.2 (some w)).1
    obtain ⟨p, hp, hl, hpen⟩ := hu
    refine bm_extend hM ⟨p, hp, hl, hpen⟩ (c := some z) hadj.symm hno ?_
    rw [bm_strong_some, Subgraph.mem_edgeSet]
    simp [hs, hzw]
  obtain ⟨u, hu⟩ := bm_has_arrow hwn hw
  have hzw : s(z, w) ∉ M.edgeSet := by
    rw [Subgraph.mem_edgeSet]
    intro hm
    have hs := hweak u hu
    apply (hz.2 (some w)).1
    refine bm_extend hM hu (c := some z) hadj.symm hno ?_
    rw [bm_strong_some, Subgraph.mem_edgeSet]
    simp [hs, hm.symm]
  refine ⟨hzw, (hz.2 (some w)).2, (hz.2 (some w)).1, hwn, ⟨u, hu, hweak u hu⟩, ?_⟩
  rintro ⟨u', hu', hs'⟩
  exact hweak u' hu' hs'

theorem lemma_4_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M)
    (Z : (G.induce {x : V | IsInaccessible G M x}).ConnectedComponent) :
    (∀ z ∈ Subtype.val '' Z.supp, ∀ w : V, w ∉ Subtype.val '' Z.supp → G.Adj z w →
        s(z, w) ∉ M.edgeSet ∧ ¬ Arrow G M (some z) (some w) ∧ ¬ Arrow G M (some w) (some z) ∧
          IsWeakPt G M w) ∧
      2 ≤ (Subtype.val '' Z.supp).ncard := by
  have part1 : ∀ z ∈ Subtype.val '' Z.supp, ∀ w : V, w ∉ Subtype.val '' Z.supp → G.Adj z w →
        s(z, w) ∉ M.edgeSet ∧ ¬ Arrow G M (some z) (some w) ∧ ¬ Arrow G M (some w) (some z) ∧
          IsWeakPt G M w := by
    rintro _ ⟨⟨z, hz⟩, hzZ, rfl⟩ w hwZ hadj
    have hw : ¬ IsInaccessible G M w := by
      intro hw
      apply hwZ
      refine ⟨⟨w, hw⟩, ?_, rfl⟩
      rw [ConnectedComponent.mem_supp_iff] at hzZ ⊢
      rw [← hzZ]
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj
        (show (G.induce {x : V | IsInaccessible G M x}).Adj ⟨z, hz⟩ ⟨w, hw⟩ from hadj)).symm
    exact bm_l4_edge hM hz hw hadj
  refine ⟨part1, ?_⟩
  obtain ⟨⟨v, hv⟩, hvZ⟩ := Quot.exists_rep Z
  have hvs : ⟨v, hv⟩ ∈ Z.supp := by
    rw [ConnectedComponent.mem_supp_iff]; exact hvZ
  obtain ⟨y, hy⟩ := bm_exists_mate hv.1
  have hvim : v ∈ Subtype.val '' Z.supp := ⟨_, hvs, rfl⟩
  have hyim : y ∈ Subtype.val '' Z.supp := by
    by_contra hyZ
    exact (part1 v hvim y hyZ (M.adj_sub hy)).1 (Subgraph.mem_edgeSet.mpr hy)
  have hne : v ≠ y := (M.adj_sub hy).ne
  rw [← Set.ncard_pair hne]
  exact Set.ncard_le_ncard (by
    intro t ht; rcases ht with rfl | rfl
    · exact hvim
    · exact hyim) (Set.toFinite _)

end L4

end BergeMatching.Core

open BergeMatching.Core


theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M)
    (Z : (G.induce {x : V | IsInaccessible G M x}).ConnectedComponent) :
    (∀ z ∈ Subtype.val '' Z.supp, ∀ w : V, w ∉ Subtype.val '' Z.supp → G.Adj z w →
        s(z, w) ∉ M.edgeSet ∧ ¬ Arrow G M (some z) (some w) ∧ ¬ Arrow G M (some w) (some z) ∧
          IsWeakPt G M w) ∧
      2 ≤ (Subtype.val '' Z.supp).ncard := by
  exact lemma_4_core G M hM h Z
