-- Prove2me | solution 1 for DeciSigma1.Semantics.fullTree_fn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:26:37.43098+00:00
-- url     : https://prove2.me/submissions/2bad80b1-b01b-45bf-8f26-862f9db063ea

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Data.List.Induction
public import Mathlib.Order.MinMax
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Median

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}
namespace DeciSigma1.Semantics
theorem _root_.solution (w : List (Fin n)) : (fullTree : Tree n).fn w = some .f := rfl
end DeciSigma1.Semantics
