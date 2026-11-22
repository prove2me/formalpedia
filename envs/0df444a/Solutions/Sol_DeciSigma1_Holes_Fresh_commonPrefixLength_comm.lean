-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.commonPrefixLength_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:08.267257+00:00
-- url     : https://prove2.me/submissions/f4bdb79e-6f4b-48d7-aae2-6a883adf6401

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_commonPrefixLength_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_commonPrefixLength_le_left
public import Theorems.Thm_DeciSigma1_Holes_Fresh_commonPrefixLength_le_right
public import Theorems.Thm_DeciSigma1_Holes_Fresh_take_commonPrefixLength

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {β : Type} [DecidableEq β]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (A B : List β) : commonPrefixLength A B = commonPrefixLength B A :=
  le_antisymm
    (le_commonPrefixLength_iff.mpr ⟨commonPrefixLength_le_right A B, commonPrefixLength_le_left A B,
        (take_commonPrefixLength A B).symm⟩)
    (le_commonPrefixLength_iff.mpr ⟨commonPrefixLength_le_right B A, commonPrefixLength_le_left B A,
        (take_commonPrefixLength B A).symm⟩)
end DeciSigma1.Holes.Fresh
