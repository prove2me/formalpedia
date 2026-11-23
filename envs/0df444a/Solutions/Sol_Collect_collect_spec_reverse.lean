-- Prove2me | solution 1 for Collect.collect_spec_reverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:59:20.996481+00:00
-- url     : https://prove2.me/submissions/f0bcbf3e-07f1-482b-a3ba-72a7279dac54

import Definitions.Def_Bdd_Basic
import Definitions.Def_Bdd_Collect
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const


section
set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace Collect
private lemma collect_helper_terminal {v : Vector (Node n m) m} {h : Bdd.Ordered {heap := v, root := .terminal b}} :
    collect_helper ⟨{heap := v, root := .terminal b}, h⟩ I = I := by
  conv =>
    lhs
    unfold collect_helper
  congr
private lemma collect_helper_terminal' {O : OBdd n m} (h : O.1.root = .terminal b) :
    collect_helper O I = I := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only at h
  have := collect_helper_terminal (h := (show Bdd.Ordered {heap := M, root := .terminal b} by simp_rw [← h]; exact o)) (I := I)
  simp_rw [h]
  assumption
private lemma collect_helper_node {v : Vector (Node n m) m} {h : Bdd.Ordered {heap := v, root := .node j}} :
    collect_helper ⟨{heap := v, root := .node j}, h⟩ I =
      if I.1[j]
      then I
      else collect_helper ⟨⟨v, v[j].high⟩, Bdd.ordered_of_relevant ⟨⟨v, .node j⟩, h⟩ ⟨v[j].high, Bdd.reachable_of_edge (Edge.high rfl)⟩⟩
                          (collect_helper ⟨{heap := v, root := v[j].low}, Bdd.ordered_of_relevant ⟨{heap := v, root := .node j}, h⟩ ⟨v[j].low, Bdd.reachable_of_edge (Edge.low rfl)⟩⟩
                                          ⟨I.1.set j true, j :: I.2⟩) := by
  conv =>
    lhs
    unfold collect_helper
  congr
private lemma collect_helper_node' (O : OBdd n m) {j : Fin m} (h : O.1.root = .node j) :
    collect_helper O I = if I.1[j] then I else collect_helper (O.high h) (collect_helper (O.low h) ⟨I.1.set j true, j :: I.2⟩) := by
  rcases O with ⟨⟨M, r⟩, o⟩
  simp only at h
  have := collect_helper_node (h := (show Bdd.Ordered {heap := M, root := .node j} by simp_rw [← h]; exact o)) (I := I)
  simp_rw [h]
  assumption
private theorem collect_helper_spec_reverse (O : OBdd n m) (r : Pointer m) I :
    Pointer.Reachable O.1.heap r O.1.root →
    (∀ i ∈ I.2, Pointer.Reachable O.1.heap r (.node i)) →
    ∀ i ∈ (collect_helper O I).2, Pointer.Reachable O.1.heap r (.node i) := by
  intro h0 h1 i h2
  cases h : O.1.root with
  | terminal b =>
    rw [collect_helper_terminal' h] at h2
    exact h1 i h2
  | node j =>
    rw [collect_helper_node' O h] at h2
    split at h2
    next ht =>
      exact h1 i h2
    next hf =>
      cases List.instDecidableMemOfLawfulBEq i (j :: I.2) with
      | isTrue htt =>
        cases htt with
        | head as    => convert h0; symm; assumption
        | tail b hin => exact h1 i hin
      | isFalse hff =>
        cases List.instDecidableMemOfLawfulBEq i (collect_helper (O.low h) (I.1.set j true, j :: I.2)).2 with
        | isFalse hhf =>
          rw [← Bdd.high_heap_eq_heap (h := h)]
          refine collect_helper_spec_reverse (O.high h) r _ ?_ ?_ i h2
          · trans O.1.root
            · exact h0
            · exact Bdd.reachable_of_edge (Bdd.edge_of_high (h := h))
          · intro i' hi'
            simp only [OBdd.high_heap_eq_heap]
            rw [← OBdd.low_heap_eq_heap (h := h)]
            refine collect_helper_spec_reverse (O.low h) r _ ?_ ?_ i' hi'
            · trans O.1.root
              · exact h0
              · exact Bdd.reachable_of_edge (Bdd.edge_of_low (h := h))
            · intro i'' hi''
              simp only at hi''
              cases hi'' with
              | head as     => simp only [OBdd.low_heap_eq_heap]; convert h0; symm; assumption
              | tail _ hi'' =>
                simp only [OBdd.low_heap_eq_heap]
                exact h1 i'' hi''
        | isTrue hht =>
          rw [← OBdd.low_heap_eq_heap (h := h)]
          refine collect_helper_spec_reverse (O.low h) r _ ?_ ?_ i hht
          · trans O.1.root
            · exact h0
            · exact OBdd.reachable_of_edge (Bdd.edge_of_low (h := h))
          · intro i' hi'
            simp only at hi'
            cases hi' with
            | head as    => simp only [OBdd.low_heap_eq_heap]; convert h0; symm; assumption
            | tail _ hi' =>
              simp only [OBdd.low_heap_eq_heap]
              exact h1 i' hi'
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end Collect
end

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Collect
namespace Collect
theorem _root_.solution {O : OBdd n m} {j : Fin m} :
    j ∈ collect O → Pointer.Reachable O.1.heap O.1.root (.node j) := by
  intro h
  simp only [collect] at h
  apply collect_helper_spec_reverse O O.1.root (Vector.replicate m false, []) (Relation.ReflTransGen.refl)
  · simp
  · assumption
end Collect
