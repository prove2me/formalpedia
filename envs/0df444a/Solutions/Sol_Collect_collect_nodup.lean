-- Prove2me | solution 1 for Collect.collect_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:54.376582+00:00
-- url     : https://prove2.me/submissions/4012b3db-a48e-4ecc-bc9c-a7bf19470549

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
private theorem collect_helper_nodup {I : Vector Bool m × List (Fin m)} {O : OBdd n m} :
    (∀ i ∈ I.2, I.1[i] = true) ∧ I.2.Nodup →
    (∀ i ∈ (collect_helper O I).2, (collect_helper O I).1[i] = true) ∧ (collect_helper O I).2.Nodup := by
  intro h
  cases O_root_def : O.1.root with
  | terminal b => simpa [collect_helper_terminal' O_root_def]
  | node     j =>
    rw [collect_helper_node' O O_root_def]
    split
    next heq => assumption
    next heq =>
      apply collect_helper_nodup
      apply collect_helper_nodup
      simp only [List.mem_cons, forall_eq_or_imp]
      constructor
      · constructor
        · simp
        · intro i hi
          cases decEq j i with
          | isFalse hf =>
            simp only [Fin.getElem_fin]
            rw [Vector.getElem_set_ne _ _ (by simp_all [Fin.val_ne_of_ne hf])]
            exact h.1 i hi
          | isTrue  ht => simp_all
      · constructor
        · contrapose heq
          simp_all
        · exact h.2
termination_by O
decreasing_by all_goals first | exact oedge_of_low | exact oedge_of_high | decreasing_tactic
end Collect
end

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Collect
namespace Collect
theorem _root_.solution {O : OBdd n m} : (collect O).Nodup := by
  simp only [collect]
  exact (collect_helper_nodup (by simp)).2
end Collect
