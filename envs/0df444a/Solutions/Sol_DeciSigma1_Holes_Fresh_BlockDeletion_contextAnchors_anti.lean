-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.contextAnchors_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:25:48.209802+00:00
-- url     : https://prove2.me/submissions/848308b6-f7d1-49e3-aef5-bacc77d096ac

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelPreservation
public import Theorems.Thm_DeciSigma1_Holes_Fresh_contextAnchors_succ_subset
public import Theorems.Thm_DeciSigma1_Readers_Dominates_refl
public import Theorems.Thm_DeciSigma1_Readers_Dominates_trans
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_refl
public import Theorems.Thm_DeciSigma1_Readers_FreshDominates_trans


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
theorem _root_.solution {s t' : ℕ} (h : s ≤ t') (u : List α) :
    contextAnchors W t' u ⊆ contextAnchors W s u := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact (contextAnchors_succ_subset _ u).trans ih
end DeciSigma1.Holes.Fresh.BlockDeletion
