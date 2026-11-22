-- Prove2me | solution 1 for DeciSigma1.Semantics.medianSym_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:36:51.899771+00:00
-- url     : https://prove2.me/submissions/33188c14-8d80-4893-828f-994c76708625

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
theorem _root_.solution (a b c : Sym) :
    Sym.flip true (medianSym a b c) =
      medianSym (Sym.flip true a) (Sym.flip true b) (Sym.flip true c) := by
  cases a <;> cases b <;> cases c <;> decide
end DeciSigma1.Semantics
