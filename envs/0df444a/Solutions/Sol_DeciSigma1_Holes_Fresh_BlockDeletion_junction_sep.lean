-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.junction_sep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:34:22.573922+00:00
-- url     : https://prove2.me/submissions/4a5a88ea-5ec3-404d-bfe3-34aa9569ff2b

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_junction_window

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
theorem _root_.solution {l : Fin k} {u u' : ℕ} (hu : IsJunction m.deletionLength (m.sites l) u)
        (hu' : IsJunction m.deletionLength (m.sites l) u')
        (hlt : u < u') :
    u + m.upperCutLength ≤ u' := by
  obtain ⟨c, hc, rfl⟩ := hu
  rcases (m.junction_window hc).2.1 u' hu' with h | h
  · omega
  · exact h
end DeciSigma1.Holes.Fresh.BlockDeletion
