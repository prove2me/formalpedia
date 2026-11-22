-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.commonPrefixLength_le_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:30.50562+00:00
-- url     : https://prove2.me/submissions/d1811e41-a851-4d0f-8def-62b32e966ed6

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
    commonPrefixLength A B ≤ B.length := (le_commonPrefixLength_iff.mp le_rfl).2.1
end DeciSigma1.Holes.Fresh
