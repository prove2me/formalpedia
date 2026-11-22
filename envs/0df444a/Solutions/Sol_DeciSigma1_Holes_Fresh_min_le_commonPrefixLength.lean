-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.min_le_commonPrefixLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:04.638491+00:00
-- url     : https://prove2.me/submissions/38869f9e-bd80-45c8-a6f8-47238a40600c

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Theorems.Thm_DeciSigma1_Holes_Fresh_le_commonPrefixLength_iff
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {β : Type} [DecidableEq β]
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution (A B C : List β) :
    min (commonPrefixLength A B) (commonPrefixLength B C) ≤ commonPrefixLength A C := by
  obtain ⟨h1, h2, h3⟩ :=
      le_commonPrefixLength_iff.mp (min_le_left (commonPrefixLength A B) (commonPrefixLength B C))
  obtain ⟨h4, h5, h6⟩ :=
      le_commonPrefixLength_iff.mp (min_le_right (commonPrefixLength A B) (commonPrefixLength B C))
  exact le_commonPrefixLength_iff.mpr ⟨h1, h5, h3.trans h6⟩
end DeciSigma1.Holes.Fresh
