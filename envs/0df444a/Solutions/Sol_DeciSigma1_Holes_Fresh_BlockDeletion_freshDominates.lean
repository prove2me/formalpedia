-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.freshDominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:25.484098+00:00
-- url     : https://prove2.me/submissions/55bbd93d-8376-4c50-816c-4355f918cd53

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_channel
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_freshDominates_of_channel


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
theorem _root_.solution [DecidableEq S] (hfr : ∀ i, T.Fresh W i) :
    FreshDominates T m.apply W :=
  m.freshDominates_of_channel hfr (m.channel hfr)
end DeciSigma1.Holes.Fresh.BlockDeletion
