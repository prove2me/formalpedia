-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.commonPrefixLength_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:17:51.71474+00:00
-- url     : https://prove2.me/submissions/74143c0b-eccf-4c68-b1c6-c236e1f5e954

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_commonPrefixLength_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_commonPrefixLength_le_left

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {β : Type} [DecidableEq β]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (A : List β) : commonPrefixLength A A = A.length :=
  le_antisymm (commonPrefixLength_le_left A A) (le_commonPrefixLength_iff.mpr ⟨le_rfl, le_rfl, rfl⟩)
end DeciSigma1.Holes.Fresh
