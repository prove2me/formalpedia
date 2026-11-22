-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.active_t_of_through
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:43.755665+00:00
-- url     : https://prove2.me/submissions/5402a1b5-164a-4099-a6bc-10ea99cea5b4

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_active_of_through
public import Theorems.Thm_DeciSigma1_Holes_Fresh_active_succ_subset


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
theorem _root_.solution {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : m.edge.TraversedBy o) : o.1 ∈ active W t :=
  active_succ_subset W t (m.active_of_through ho hth)
end DeciSigma1.Holes.Fresh.BlockDeletion
