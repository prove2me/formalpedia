-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.trace_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:15:38.637832+00:00
-- url     : https://prove2.me/submissions/bb192509-4675-4b8e-96c4-2c9a4ab5b59c

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
public import Theorems.Thm_DeciSigma1_Semantics_Tree_descend_mono

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution {t u : Tree n} (h : t ≤ u) (ν : List (Fin n)) :
    trace t ν ≤ trace u ν := by
  induction ν generalizing t u with
  | nil => exact h
  | cons i ν ih => exact ih (descend_mono h i)
end DeciSigma1.Semantics.Tree
