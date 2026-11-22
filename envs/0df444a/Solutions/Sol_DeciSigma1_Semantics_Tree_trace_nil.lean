-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.trace_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:35:42.736684+00:00
-- url     : https://prove2.me/submissions/b02a50cd-746a-4d5d-88d4-811218fcaacb

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree
namespace DeciSigma1.Semantics.Tree
theorem _root_.solution (t : Tree n) : trace t [] = t := rfl
end DeciSigma1.Semantics.Tree
