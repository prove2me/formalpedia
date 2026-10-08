-- Prove2me | solution 1 for BergeMatching.Core.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:04:34.434292+00:00
-- url     : https://prove2.me/submissions/73b111de-7911-46e7-a346-05d938ced5ec

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
section L2
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {M : G.Subgraph}

lemma bm_NN (h : AbarInaccessible G M) {x y : V} (hx : IsNeutral M x) (hy : IsNeutral M y)
    (hxy : G.Adj x y) : False := by
  apply h (some y)
  have hne : x ≠ y := hxy.ne
  have h1 : s(none, some x) ∈ barStrong M := (bm_strong_none x).mpr hx
  have h3 : s(some y, none) ∈ barStrong M := by
    rw [Sym2.eq_swap]; exact (bm_strong_none y).mpr hy
  have h2 : s(some x, some y) ∉ barStrong M := by
    rw [bm_strong_some, Subgraph.mem_edgeSet]; exact bm_neutral_not_adj hx
  refine ⟨Walk.cons (show (barGraph G M).Adj none (some x) from hx)
    (Walk.cons (show (barGraph G M).Adj (some x) (some y) from hxy)
      (Walk.cons (show (barGraph G M).Adj (some y) none from hy) Walk.nil)), ⟨?_, ?_⟩,
    by simp, rfl⟩
  · rw [Walk.isTrail_def]; simp [hne]
  · simp [h1, h2, h3]

lemma bm_S_strong (hM : M.IsMatching) {x : V} (hx : IsStrongPt G M x) {z : Option V}
    (hz : Arrow G M z (some x)) : ∃ x', z = some x' ∧ M.Adj x x' := by
  apply bm_strong_nonneutral hM hx.1
  by_contra hc
  exact hx.2.2 ⟨z, hz, hc⟩

lemma bm_l2_aux (hM : M.IsMatching) {x y : V} (hx : IsStrongPt G M x ∨ IsNeutral M x)
    (hy : IsStrongPt G M y) (hxy : G.Adj x y) : False := by
  rcases hx with hx | hx
  · obtain ⟨t, ht, Q, hQ, hfirst⟩ := bm_first_visit ({x, y} : Set V)
      ⟨x, by simp, hx.2.1.elim fun z hz => ⟨z, hz.1⟩⟩
    have key : ∀ t o : V, IsStrongPt G M t → IsStrongPt G M o → G.Adj t o →
        (Q' : (barGraph G M).Walk none (some t)) → IsAlternatingWrt (barStrong M) Q' →
        some o ∉ Q'.support → False := by
      intro t o ht ho hto Q' hQ' hos
      have hA : Arrow G M Q'.penultimate (some t) := ⟨Q', hQ', bm_len_ne_zero Q', rfl⟩
      obtain ⟨t', ht', hmt⟩ := bm_S_strong hM ht hA
      have hnil : ¬ Q'.Nil := by rw [Walk.nil_iff_length_eq]; exact bm_len_ne_zero Q'
      have hpen : Q'.penultimate ∈ Q'.support :=
        Q'.fst_mem_support_of_mem_edges (Q'.mk_penultimate_end_mem_edges hnil)
      have hnot : ¬ M.Adj t o := by
        intro hm
        have := bm_mate_unique hM hmt hm
        subst this
        rw [ht'] at hpen
        exact hos hpen
      have hedge : s(some t, some o) ∉ Q'.edges := fun he =>
        hos (Q'.snd_mem_support_of_mem_edges he)
      have halt : s(Q'.penultimate, some t) ∈ barStrong M ↔ s(some t, some o) ∉ barStrong M := by
        rw [ht', bm_strong_some, bm_strong_some, Subgraph.mem_edgeSet, Subgraph.mem_edgeSet]
        exact ⟨fun _ => hnot, fun _ => hmt.symm⟩
      have hto' : (barGraph G M).Adj (some t) (some o) := hto
      have hB : Arrow G M (some t) (some o) :=
        ⟨Q'.concat hto', bm_alt_concat hQ' hnil hto' hedge halt, by simp,
          by simp [Walk.penultimate_concat]⟩
      exact ho.2.2 ⟨_, hB, by rw [bm_strong_some, Subgraph.mem_edgeSet]; exact hnot⟩
    have hne : x ≠ y := hxy.ne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact key t y hx hy hxy Q hQ (fun hm => hne (hfirst y (by simp) hm).symm)
    · exact key t x hy hx hxy.symm Q hQ (fun hm => hne (hfirst x (by simp) hm))
  · exact hy.2.2 ⟨_, bm_arrow_neutral hx hxy, by
      rw [bm_strong_some, Subgraph.mem_edgeSet]; exact bm_neutral_not_adj hx⟩

theorem lemma_2_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M) :
    G.IsIndepSet ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x}) := by
  intro x hx y hy _ hxy
  simp only [Set.mem_union, Set.mem_setOf_eq] at hx hy
  rcases hy with hy | hy
  · exact bm_l2_aux hM hx hy hxy
  · rcases hx with hx | hx
    · exact bm_l2_aux hM (Or.inr hy) hx hxy.symm
    · exact bm_NN h hx hy hxy

end L2

end BergeMatching.Core

open BergeMatching.Core


theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M) :
    G.IsIndepSet ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x}) := by
  exact lemma_2_core G M hM h
