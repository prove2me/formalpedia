-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.minDepth_le_endDepth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:51:05.284441+00:00
-- url     : https://prove2.me/submissions/add58cfc-c48e-4081-a6bf-b9a63bd97963

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_maxDepth_lt_endDepth


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
theorem _root_.solution :
    m.minDepth ≤
        m.edge.endDepth := by have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth;
                              omega
end DeciSigma1.Holes.Fresh.BlockDeletion
