-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.commonSuffixLength_mem_trieNodes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:18:20.161805+00:00
-- url     : https://prove2.me/submissions/402eea8c-1548-4475-9df5-035af7a9084d

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
namespace DeciSigma1.Holes.Fresh
theorem _root_.solution {W : Fin k → List α} {t : ℕ} (Z : List (List α))
    {Y : List (List α)} (hY : Y ∈ upperParses W t) : commonSuffixLength Z Y ∈ trieNodes W t Z :=
  mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ hY))
end DeciSigma1.Holes.Fresh
