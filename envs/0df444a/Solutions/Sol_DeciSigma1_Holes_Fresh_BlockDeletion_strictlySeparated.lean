-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.strictlySeparated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:32:42.247523+00:00
-- url     : https://prove2.me/submissions/50377dd6-30a7-4f32-a0f9-a02af12d08c6

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_sites_separated

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution (l : Fin k) :
    StrictlySeparated m.deletionLength (m.sites l) :=
  fun _ hc _ hc' h => m.sites_separated hc hc' h
end DeciSigma1.Holes.Fresh.BlockDeletion
