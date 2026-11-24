-- Prove2me | solution 1 for FockSPR.blocks_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:29.162097+00:00
-- url     : https://prove2.me/submissions/26d54d8f-1ccb-49b7-acf1-d32f459b0f59

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition

set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution (D : ℕ) (n : ℕ) (hn : 1 ≤ n) (_hnD : n ≤ D) :
    ∃ ℓ, 1 ≤ ℓ ∧ n ∈ freqBlock ℓ := by
  refine ⟨Nat.sqrt n, ?_, ?_⟩
  · exact Nat.sqrt_pos.mpr (by omega)
  · simp only [freqBlock, Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have := Nat.sqrt_le n; linarith only [this]
    · have h1 := Nat.lt_succ_sqrt' n
      simp only [Nat.succ_eq_add_one] at h1; omega
end FockSPR
