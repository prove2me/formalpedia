-- Prove2me | solution 1 for Collect.collect_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:48.765874+00:00
-- url     : https://prove2.me/submissions/47fa1c3f-5464-458b-93c4-0ab903bb84c6

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
end Collect
end

set_option autoImplicit true
attribute [local instance_reducible] OBdd Bdd.Ordered
open Collect
namespace Collect
theorem _root_.solution {O : OBdd n m} (h : O.1.root = .terminal b) :
    collect O = [] := by
  simp only [collect, collect_helper_terminal' h]
end Collect
