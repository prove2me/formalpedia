-- Prove2me | solution 1 for BergeMatching.Core.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T20:06:56.590216+00:00
-- url     : https://prove2.me/submissions/de3ada00-3bda-4ee3-984f-76c8a7dfc4c1

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
section L3
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}

lemma bm_matching_edge_unique {M' : G.Subgraph} (hM' : M'.IsMatching) {e1 e2 : Sym2 V} {v : V}
    (h1 : e1 ∈ M'.edgeSet) (h2 : e2 ∈ M'.edgeSet) (hv1 : v ∈ e1) (hv2 : v ∈ e2) : e1 = e2 := by
  have key : ∀ e ∈ M'.edgeSet, v ∈ e → ∃ w, M'.Adj v w ∧ e = s(v, w) := by
    intro e he hve
    induction e using Sym2.ind with
    | h a b =>
      rw [Subgraph.mem_edgeSet] at he
      rcases Sym2.mem_iff.mp hve with rfl | rfl
      · exact ⟨b, he, rfl⟩
      · exact ⟨a, he.symm, Sym2.eq_swap⟩
  obtain ⟨w1, hw1, rfl⟩ := key e1 h1 hv1
  obtain ⟨w2, hw2, rfl⟩ := key e2 h2 hv2
  rw [bm_mate_unique hM' hw1 hw2]

lemma bm_matching_le_cover [Finite V] {M' : G.Subgraph} (hM' : M'.IsMatching) {D : Set V}
    (hD : G.IsVertexCover D) : M'.edgeSet.ncard ≤ D.ncard := by
  classical
  let f : Sym2 V → V := fun e => if e.out.1 ∈ D then e.out.1 else e.out.2
  have hrep : ∀ e : Sym2 V, s(e.out.1, e.out.2) = e := fun e => Quot.out_eq e
  have hf : ∀ e ∈ M'.edgeSet, f e ∈ D ∧ f e ∈ e := by
    intro e he
    have he' := he
    rw [← hrep e, Subgraph.mem_edgeSet] at he'
    have hmem1 : e.out.1 ∈ e := by
      have := Sym2.mem_mk_left e.out.1 e.out.2; rwa [hrep e] at this
    have hmem2 : e.out.2 ∈ e := by
      have := Sym2.mem_mk_right e.out.1 e.out.2; rwa [hrep e] at this
    simp only [f]
    split_ifs with hc
    · exact ⟨hc, hmem1⟩
    · rcases hD (M'.adj_sub he') with h | h
      · exact absurd h hc
      · exact ⟨h, hmem2⟩
  refine Set.ncard_le_ncard_of_injOn f (fun e he => (hf e he).1) ?_
  intro e1 he1 e2 he2 heq
  exact bm_matching_edge_unique hM' he1 he2 (hf e1 he1).2 (heq ▸ (hf e2 he2).2)

lemma bm_has_arrow {M : G.Subgraph} {x : V} (hx : ¬ IsNeutral M x) (hI : ¬ IsInaccessible G M x) :
    ∃ z, Arrow G M z (some x) := by
  unfold IsInaccessible at hI
  push_neg at hI
  obtain ⟨y, hy⟩ := hI hx
  by_cases h : Arrow G M y (some x)
  · exact ⟨y, h⟩
  · exact bm_arrow_into_of_arrow_from (hy h)

theorem lemma_3_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M)
    (hMed : {x : V | IsMedium G M x} = ∅) (hI : {x : V | IsInaccessible G M x} = ∅) :
    IsMaximumIndepSet G ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x}) ∧
      IsMinimumVertexCover G {x : V | IsWeakPt G M x} ∧
      IsMaximumMatching M := by
  classical
  have hnoMed : ∀ x, ¬ IsMedium G M x := fun x hx => by
    have : x ∈ {x : V | IsMedium G M x} := hx
    rw [hMed] at this; exact this
  have hnoI : ∀ x, ¬ IsInaccessible G M x := fun x hx => by
    have : x ∈ {x : V | IsInaccessible G M x} := hx
    rw [hI] at this; exact this
  have hclass : ∀ x, ¬ IsNeutral M x → (IsStrongPt G M x ∨ IsWeakPt G M x) := by
    intro x hx
    obtain ⟨z, hz⟩ := bm_has_arrow hx (hnoI x)
    by_cases hs : ∃ z, Arrow G M z (some x) ∧ s(z, some x) ∈ barStrong M
    · by_cases hw : ∃ z, Arrow G M z (some x) ∧ s(z, some x) ∉ barStrong M
      · exact absurd ⟨hx, hs, hw⟩ (hnoMed x)
      · exact Or.inl ⟨hx, hs, hw⟩
    · right
      exact ⟨hx, ⟨z, hz, fun hzs => hs ⟨z, hz, hzs⟩⟩, hs⟩
  have hAW : ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x})ᶜ =
      {x : V | IsWeakPt G M x} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or]
    constructor
    · rintro ⟨hS, hN⟩
      rcases hclass x hN with h1 | h1
      · exact absurd h1 hS
      · exact h1
    · intro hx
      exact ⟨fun hS => hS.2.2 hx.2.1, hx.1⟩
  have hmatchW : ∀ x y, M.Adj x y → IsWeakPt G M x → IsWeakPt G M y → False := by
    intro x y hxy hx hy
    obtain ⟨t, ht, Q, hQ, hfirst⟩ := bm_first_visit ({x, y} : Set V)
      ⟨x, by simp, hx.2.1.elim fun z hz => ⟨z, hz.1⟩⟩
    have key : ∀ t o : V, M.Adj t o → IsWeakPt G M t → IsWeakPt G M o →
        (Q' : (barGraph G M).Walk none (some t)) → IsAlternatingWrt (barStrong M) Q' →
        some o ∉ Q'.support → False := by
      intro t o hto ht ho Q' hQ' hos
      have hA : Arrow G M Q'.penultimate (some t) := ⟨Q', hQ', bm_len_ne_zero Q', rfl⟩
      have hweak : s(Q'.penultimate, some t) ∉ barStrong M := fun hs => ht.2.2 ⟨_, hA, hs⟩
      have hnil : ¬ Q'.Nil := by rw [Walk.nil_iff_length_eq]; exact bm_len_ne_zero Q'
      have hedge : s(some t, some o) ∉ Q'.edges := fun he =>
        hos (Q'.snd_mem_support_of_mem_edges he)
      have hstr : s(some t, some o) ∈ barStrong M :=
        (bm_strong_some t o).mpr (Subgraph.mem_edgeSet.mpr hto)
      have hto' : (barGraph G M).Adj (some t) (some o) := M.adj_sub hto
      have hB : Arrow G M (some t) (some o) :=
        ⟨Q'.concat hto', bm_alt_concat hQ' hnil hto' hedge (by simp [hweak, hstr]), by simp,
          by simp [Walk.penultimate_concat]⟩
      exact ho.2.2 ⟨_, hB, hstr⟩
    have hne : x ≠ y := (M.adj_sub hxy).ne
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact key t y hxy hx hy Q hQ (fun hm => hne (hfirst y (by simp) hm).symm)
    · exact key t x hxy.symm hy hx Q hQ (fun hm => hne (hfirst x (by simp) hm))
  have hmatchS : ∀ x y, M.Adj x y → ¬ IsWeakPt G M x → IsWeakPt G M y := by
    intro x y hxy hx
    have hxn : ¬ IsNeutral M x := fun hn => bm_neutral_not_adj hn hxy
    have hyn : ¬ IsNeutral M y := fun hn => bm_neutral_not_adj hn hxy.symm
    rcases hclass y hyn with hy | hy
    · rcases hclass x hxn with hx' | hx'
      · exact (bm_l2_aux hM (Or.inl hx') hy (M.adj_sub hxy)).elim
      · exact absurd hx' hx
    · exact hy
  have hcov : G.IsVertexCover {x : V | IsWeakPt G M x} := by
    rw [← hAW, isVertexCover_compl]
    exact lemma_2_core G M hM h
  have hWM : {x : V | IsWeakPt G M x}.ncard ≤ M.edgeSet.ncard := by
    let g : V → Sym2 V := fun x => if hx : ∃ y, M.Adj x y then s(x, hx.choose) else s(x, x)
    have hg : ∀ x, IsWeakPt G M x → ∃ y, M.Adj x y ∧ g x = s(x, y) := by
      intro x hx
      have hex := bm_exists_mate (G := G) (M := M) hx.1
      refine ⟨hex.choose, hex.choose_spec, ?_⟩
      simp only [g, dif_pos hex]
    refine Set.ncard_le_ncard_of_injOn g ?_ ?_
    · intro x hx
      obtain ⟨y, hy, hgy⟩ := hg x hx
      rw [hgy]; exact Subgraph.mem_edgeSet.mpr hy
    · intro x1 hx1 x2 hx2 heq
      obtain ⟨y1, hy1, hg1⟩ := hg x1 hx1
      obtain ⟨y2, hy2, hg2⟩ := hg x2 hx2
      rw [hg1, hg2, Sym2.eq_iff] at heq
      rcases heq with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · subst h2
        exact (hmatchW x1 y1 hy1 hx1 hx2).elim
  refine ⟨⟨lemma_2_core G M hM h, fun B hB => ?_⟩, ⟨hcov, fun D hD => ?_⟩,
    ⟨hM, fun M' hM' => ?_⟩⟩
  · have hBc : G.IsVertexCover Bᶜ := isVertexCover_compl.mpr hB
    have h1 := bm_matching_le_cover hM hBc
    have h2 := Set.ncard_add_ncard_compl B
    have h3 := Set.ncard_add_ncard_compl
      ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x})
    rw [hAW] at h3
    omega
  · exact hWM.trans (bm_matching_le_cover hM hD)
  · exact (bm_matching_le_cover hM' hcov).trans hWM

end L3

end BergeMatching.Core

open BergeMatching.Core


theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (M : G.Subgraph) (hM : M.IsMatching) (h : AbarInaccessible G M)
    (hMed : {x : V | IsMedium G M x} = ∅) (hI : {x : V | IsInaccessible G M x} = ∅) :
    IsMaximumIndepSet G ({x : V | IsStrongPt G M x} ∪ {x : V | IsNeutral M x}) ∧
      IsMinimumVertexCover G {x : V | IsWeakPt G M x} ∧
      IsMaximumMatching M := by
  exact lemma_3_core G M hM h hMed hI
