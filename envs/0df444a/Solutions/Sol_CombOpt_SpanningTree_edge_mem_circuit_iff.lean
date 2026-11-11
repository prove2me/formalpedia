-- Prove2me | solution 1 for CombOpt.SpanningTree.edge_mem_circuit_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T06:15:43.854681+00:00
-- url     : https://prove2.me/submissions/c916ea4f-31c8-46af-a4fe-a4f06ffd0387

import Mathlib
import Definitions.Def_CombOpt_SpanningTree_Graph_IsCircuit

namespace Aux_SPTC
open CombOpt.SpanningTree

variable {V E : Type*} {G : CombOpt.SpanningTree.Graph V E}

def wappend : {a b c : V} → G.Walk a b → G.Walk b c → G.Walk a c
  | _, _, _, .nil _, q => q
  | _, _, _, .cons e h p, q => .cons e h (wappend p q)

def wrev : {a b : V} → G.Walk a b → G.Walk b a
  | _, _, .nil v => .nil v
  | a, _, .cons e h p => wappend (wrev p) (.cons e (h.trans Sym2.eq_swap) (.nil a))

lemma edges_wappend : ∀ {a b c : V} (p : G.Walk a b) (q : G.Walk b c),
    (wappend p q).edges = p.edges ++ q.edges
  | _, _, _, .nil _, q => by simp [wappend, CombOpt.SpanningTree.Graph.Walk.edges]
  | _, _, _, .cons e h p, q => by simp [wappend, CombOpt.SpanningTree.Graph.Walk.edges, edges_wappend p q]

lemma edges_wrev : ∀ {a b : V} (p : G.Walk a b), (wrev p).edges = p.edges.reverse
  | _, _, .nil _ => by simp [wrev, CombOpt.SpanningTree.Graph.Walk.edges]
  | _, _, .cons e h p => by simp [wrev, edges_wappend, edges_wrev p, CombOpt.SpanningTree.Graph.Walk.edges]

lemma support_eq : ∀ {a b : V} (p : G.Walk a b), p.support = a :: p.support.tail
  | _, _, .nil _ => by simp [CombOpt.SpanningTree.Graph.Walk.support]
  | _, _, .cons _ _ _ => by simp [CombOpt.SpanningTree.Graph.Walk.support]

lemma support_wappend : ∀ {a b c : V} (p : G.Walk a b) (q : G.Walk b c),
    (wappend p q).support = p.support ++ q.support.tail
  | _, _, _, .nil _, q => by
      simp only [wappend, CombOpt.SpanningTree.Graph.Walk.support]
      exact support_eq q
  | _, _, _, .cons e h p, q => by
      simp [wappend, CombOpt.SpanningTree.Graph.Walk.support, support_wappend p q]

lemma support_wrev : ∀ {a b : V} (p : G.Walk a b), (wrev p).support = p.support.reverse
  | _, _, .nil _ => by simp [wrev, CombOpt.SpanningTree.Graph.Walk.support]
  | _, _, .cons e h p => by
      simp [wrev, support_wappend, support_wrev p, CombOpt.SpanningTree.Graph.Walk.support]

lemma ends_mem_support : ∀ {a b : V} (p : G.Walk a b) (x : E), x ∈ p.edges →
    ∀ y, y ∈ G.ends x → y ∈ p.support
  | _, _, .nil _, x, hx, _, _ => by simp [CombOpt.SpanningTree.Graph.Walk.edges] at hx
  | a, _, .cons e h p, x, hx, y, hy => by
      simp only [CombOpt.SpanningTree.Graph.Walk.edges, List.mem_cons] at hx
      simp only [CombOpt.SpanningTree.Graph.Walk.support, List.mem_cons]
      rcases hx with rfl | hx
      · rw [h, Sym2.mem_iff] at hy
        rcases hy with rfl | rfl
        · left; rfl
        · right; rw [support_eq p]; exact List.mem_cons_self
      · right; exact ends_mem_support p x hx y hy

lemma edges_nodup_of_support : ∀ {a b : V} (p : G.Walk a b), p.support.Nodup → p.edges.Nodup
  | _, _, .nil _, _ => by simp [CombOpt.SpanningTree.Graph.Walk.edges]
  | a, _, .cons e h p, hs => by
      simp only [CombOpt.SpanningTree.Graph.Walk.support, List.nodup_cons] at hs
      simp only [CombOpt.SpanningTree.Graph.Walk.edges, List.nodup_cons]
      refine ⟨fun he => hs.1 (ends_mem_support p e he a ?_), edges_nodup_of_support p hs.2⟩
      rw [h]; exact Sym2.mem_mk_left a _

lemma suffix : ∀ {a b : V} (q : G.Walk a b) (x : V), x ∈ q.support →
    ∃ r : G.Walk x b, r.support.Sublist q.support ∧ ∀ f ∈ r.edges, f ∈ q.edges
  | _, _, .nil _, x, hx => by
      simp only [CombOpt.SpanningTree.Graph.Walk.support, List.mem_singleton] at hx
      subst hx
      exact ⟨.nil _, List.Sublist.refl _, fun f hf => hf⟩
  | a, _, .cons e h p, x, hx => by
      by_cases hxa : x = a
      · subst hxa
        exact ⟨.cons e h p, List.Sublist.refl _, fun f hf => hf⟩
      · simp only [CombOpt.SpanningTree.Graph.Walk.support, List.mem_cons] at hx
        rcases hx with hx | hx
        · exact absurd hx hxa
        · obtain ⟨r, hr1, hr2⟩ := suffix p x hx
          refine ⟨r, ?_, fun f hf => ?_⟩
          · simp only [CombOpt.SpanningTree.Graph.Walk.support]
            exact hr1.trans (List.sublist_cons_self _ _)
          · simp only [CombOpt.SpanningTree.Graph.Walk.edges, List.mem_cons]
            right; exact hr2 f hf

lemma shorten : ∀ {a b : V} (p : G.Walk a b),
    ∃ q : G.Walk a b, q.support.Nodup ∧ ∀ f ∈ q.edges, f ∈ p.edges
  | _, _, .nil v => ⟨.nil v, by simp [CombOpt.SpanningTree.Graph.Walk.support], fun f hf => hf⟩
  | a, _, .cons e h p => by
      obtain ⟨q, hq1, hq2⟩ := shorten p
      by_cases ha : a ∈ q.support
      · obtain ⟨r, hr1, hr2⟩ := suffix q a ha
        refine ⟨r, hr1.nodup hq1, fun f hf => ?_⟩
        simp only [CombOpt.SpanningTree.Graph.Walk.edges, List.mem_cons]
        right; exact hq2 f (hr2 f hf)
      · refine ⟨.cons e h q, ?_, fun f hf => ?_⟩
        · simp only [CombOpt.SpanningTree.Graph.Walk.support, List.nodup_cons]
          exact ⟨ha, hq1⟩
        · simp only [CombOpt.SpanningTree.Graph.Walk.edges, List.mem_cons] at hf ⊢
          rcases hf with hf | hf
          · left; exact hf
          · right; exact hq2 f hf

lemma split : ∀ {a b : V} (p : G.Walk a b) (e : E), e ∈ p.edges →
    ∃ (x y : V) (_ : G.ends e = s(x, y)) (p1 : G.Walk a x) (p2 : G.Walk y b),
      p.edges = p1.edges ++ e :: p2.edges
  | _, _, .nil _, e, he => by simp [CombOpt.SpanningTree.Graph.Walk.edges] at he
  | a, _, .cons e' h p, e, he => by
      by_cases hee : e = e'
      · subst hee
        exact ⟨a, _, h, .nil a, p, by simp [CombOpt.SpanningTree.Graph.Walk.edges]⟩
      · simp only [CombOpt.SpanningTree.Graph.Walk.edges, List.mem_cons] at he
        rcases he with he | he
        · exact absurd he hee
        · obtain ⟨x, y, hxy, p1, p2, hp⟩ := split p e he
          exact ⟨x, y, hxy, .cons e' h p1, p2, by simp [CombOpt.SpanningTree.Graph.Walk.edges, hp]⟩

end Aux_SPTC

open CombOpt.SpanningTree in
theorem solution {V E : Type*} [Fintype V] [Fintype E] (G : CombOpt.SpanningTree.Graph V E) (e : E)
    (u v : V) (he : G.ends e = s(u, v)) :
    (∃ (w : V) (p : G.Walk w w), G.IsCircuit p ∧ e ∈ p.edges) ↔
      ∃ p : G.Walk u v, e ∉ p.edges := by
  constructor
  · rintro ⟨w, p, ⟨hnd, -, -⟩, hmem⟩
    obtain ⟨x, y, hxy, p1, p2, hp⟩ := Aux_SPTC.split p e hmem
    rw [hp] at hnd
    have hn : e ∉ p1.edges ++ p2.edges := (List.nodup_cons.mp (List.nodup_middle.mp hnd)).1
    have hr : e ∉ (Aux_SPTC.wappend p2 p1).edges := by
      rw [Aux_SPTC.edges_wappend]
      intro h
      apply hn
      rw [List.mem_append] at h ⊢
      exact h.symm
    rw [hxy] at he
    rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨Aux_SPTC.wrev (Aux_SPTC.wappend p2 p1), ?_⟩
      rw [Aux_SPTC.edges_wrev, List.mem_reverse]
      exact hr
    · exact ⟨Aux_SPTC.wappend p2 p1, hr⟩
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq1, hq2⟩ := Aux_SPTC.shorten p
    have heq : e ∉ q.edges := fun h => hp (hq2 e h)
    refine ⟨u, .cons e he (Aux_SPTC.wrev q), ⟨?_, ?_, ?_⟩, ?_⟩
    · simp only [CombOpt.SpanningTree.Graph.Walk.edges, Aux_SPTC.edges_wrev]
      rw [List.nodup_cons, List.mem_reverse, List.nodup_reverse]
      exact ⟨heq, Aux_SPTC.edges_nodup_of_support q hq1⟩
    · simp only [CombOpt.SpanningTree.Graph.Walk.support, Aux_SPTC.support_wrev]
      obtain ⟨t, ht⟩ : ∃ t, q.support = u :: t := ⟨_, Aux_SPTC.support_eq q⟩
      rw [ht] at hq1 ⊢
      rw [List.reverse_cons, ← List.cons_append, List.dropLast_concat, List.nodup_cons,
        List.mem_reverse, List.nodup_reverse]
      exact List.nodup_cons.mp hq1
    · simp [CombOpt.SpanningTree.Graph.Walk.edges]
    · simp [CombOpt.SpanningTree.Graph.Walk.edges]
