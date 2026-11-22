-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.one_le_minDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:03:47.489233+00:00
-- url     : https://prove2.me/submissions/7fa6ccd4-f0ff-4b9c-bb18-fbf70177e6a2

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion

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
theorem _root_.solution :
    1 ≤ m.minDepth := by have := m.left_margin; unfold deletionMargin at this; omega
end DeciSigma1.Holes.Fresh.BlockDeletion
