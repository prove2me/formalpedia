-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.take_commonPrefixLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:32.20212+00:00
-- url     : https://prove2.me/submissions/566833a9-cd37-42b9-9d4d-42b5adc34c96

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_commonPrefixLength_iff

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {β : Type} [DecidableEq β]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (A B : List β) :
    A.take (commonPrefixLength A B) = B.take (commonPrefixLength A B) :=
  (le_commonPrefixLength_iff.mp le_rfl).2.2
end DeciSigma1.Holes.Fresh
