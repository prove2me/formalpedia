-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.site_occ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:56.965265+00:00
-- url     : https://prove2.me/submissions/19b4ca42-f83d-4a8c-b60b-6bedd8bb43ed

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_mem_sites


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
theorem _root_.solution {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    ∃ o ∈ upperOccurrences W t, o.1 = l ∧ m.edge.TraversedBy o ∧ depthCut W t o m.maxDepth = c :=
  m.mem_sites.mp hc
end DeciSigma1.Holes.Fresh.BlockDeletion
