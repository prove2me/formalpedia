-- Prove2me | solution 1 for DeciSigma1.Semantics.Tree.trace_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:35:58.947664+00:00
-- url     : https://prove2.me/submissions/9022d7c2-df02-477a-9404-af6ce7345194

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
theorem _root_.solution (t : Tree n) (i : Fin n) (ν : List (Fin n)) :
    trace t (i :: ν) = trace (descend t i) ν := rfl
end DeciSigma1.Semantics.Tree
