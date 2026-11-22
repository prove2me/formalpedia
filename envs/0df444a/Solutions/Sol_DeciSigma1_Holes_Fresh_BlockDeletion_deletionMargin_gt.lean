-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.deletionMargin_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:09.524955+00:00
-- url     : https://prove2.me/submissions/0042950c-2f5a-48b0-8188-6ae0bab745e5

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]
open DeciSigma1.Holes.Fresh.BlockDeletion
variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)
namespace DeciSigma1.Holes.Fresh.BlockDeletion
theorem _root_.solution
    (hlt : m.edge.startDepth + deletionMargin k (Fintype.card S) ≤ m.minDepth) :
    k * (Fintype.card S - 1) + 4 + m.edge.startDepth < m.minDepth := by
  unfold deletionMargin at hlt; omega
end DeciSigma1.Holes.Fresh.BlockDeletion
