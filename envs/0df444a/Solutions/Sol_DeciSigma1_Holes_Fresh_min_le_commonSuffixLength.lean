-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.min_le_commonSuffixLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:44.697353+00:00
-- url     : https://prove2.me/submissions/2383c07e-215d-4205-8a9e-7c700534f354

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_min_le_commonPrefixLength

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {β : Type} [DecidableEq β]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (A B C : List β) :
    min (commonSuffixLength A B) (commonSuffixLength B C) ≤ commonSuffixLength A C :=
  min_le_commonPrefixLength _ _ _
end DeciSigma1.Holes.Fresh
