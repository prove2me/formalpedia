-- Prove2me | solution 1 for ConfFamily.union_pair_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:38:37.091706+00:00
-- url     : https://prove2.me/submissions/c9f3ab6e-65ff-4aab-85a7-3570970cf4a1

import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Basic
import Definitions.Def_EventStructures_Family_Basic

set_option autoImplicit true
open ConfFamily
variable {L : Type*} (F : ConfFamily L)
variable {F}
variable (F)
namespace ConfFamily
theorem _root_.solution {α : Type*} (s : Set α) (a b : α) :
    s ∪ {a} ∪ {b} = s ∪ {b} ∪ {a} := by
  ext x; simp only [Set.mem_union, Set.mem_singleton_iff]; tauto
end ConfFamily
