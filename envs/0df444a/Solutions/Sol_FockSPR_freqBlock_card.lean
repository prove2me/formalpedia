-- Prove2me | solution 1 for FockSPR.freqBlock_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:07:56.790467+00:00
-- url     : https://prove2.me/submissions/25aaabf1-dc0c-432b-87cf-2ecc51d13f8f

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
theorem _root_.solution (ℓ : ℕ) : (freqBlock ℓ).card = 2 * ℓ + 1 := by
  simp only [freqBlock]; rw [Nat.card_Icc]
  have h : (ℓ + 1) ^ 2 = ℓ ^ 2 + 2 * ℓ + 1 := by ring
  omega
end FockSPR
