-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.depthCut_anti
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:47:22.090707+00:00
-- url     : https://prove2.me/submissions/16ef9fc2-cb9e-4397-95b7-7178559e02b1

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_depthCut_lt_of_lt


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
    {d d' : ℕ} (h : d ≤ d') (hd' : d' ≤ lowerBlockCount W t o) : depthCut W t o d' ≤
        depthCut W t o d := by
  rcases Nat.eq_or_lt_of_le h with h | h
  · rw [h]
  · exact (depthCut_lt_of_lt ho h hd').le
end DeciSigma1.Holes.Fresh.BlockDeletion
