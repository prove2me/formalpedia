-- Prove2me | solution 1 for DeciSigma1.Holes.Fresh.BlockDeletion.site_text
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:33:13.195706+00:00
-- url     : https://prove2.me/submissions/60d629b4-6b67-46df-b243-c88d9fb1eb65

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_DeletionCoordinates
public import Mathlib.Order.Nat
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ChannelTransport
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_occ
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_maxDepth_lt_endDepth
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_spec
public import Theorems.Thm_DeciSigma1_Holes_Fresh_BlockDeletion_site_valid
public import Theorems.Thm_DeciSigma1_Holes_Fresh_Edge_through_iff
public import Theorems.Thm_DeciSigma1_Holes_Fresh_text_depthCut


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
    c + m.deletionLength < (W l).length ∧ ((W l).drop c).take m.deletionLength = m.deletedText := by
  refine ⟨(m.site_valid hc).2.1, ?_⟩
  obtain ⟨o, ho, rfl, hth, rfl⟩ := m.site_occ hc
  have hsp := m.site_spec ho hth
  have hbn := (m.edge.through_iff.mp hth)
  have hjn : m.maxDepth ≤ lowerBlockCount W t o := by have := m.maxDepth_lt_endDepth; omega
  have ht := text_depthCut ho m.minDepth_lt_maxDepth.le hjn
  rw [show depthCut W t o m.minDepth - depthCut W t o m.maxDepth = m.deletionLength
      by omega] at ht
  rw [ht, deletedText]
  congr 3
  rw [show (reversedBlocks W t o).take m.maxDepth =
      ((reversedBlocks W t o).take m.edge.endDepth).take m.maxDepth by
      rw [List.take_take, Nat.min_eq_left m.maxDepth_lt_endDepth.le], hbn.2, List.take_take,
    Nat.min_eq_left m.maxDepth_lt_endDepth.le]
end DeciSigma1.Holes.Fresh.BlockDeletion
