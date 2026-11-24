-- Prove2me | solution 1 for FockSPR.blocks_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:21.43478+00:00
-- url     : https://prove2.me/submissions/71dc3ffd-a370-4515-bdd5-898810a8d525

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
theorem _root_.solution {ℓ₁ ℓ₂ : ℕ} (h₁ : 1 ≤ ℓ₁) (h₂ : 1 ≤ ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    Disjoint (freqBlock ℓ₁) (freqBlock ℓ₂) := by
  rw [Finset.disjoint_left]
  intro a ha₁ ha₂
  simp only [freqBlock, Finset.mem_Icc] at ha₁ ha₂
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hle : ℓ₁ + 1 ≤ ℓ₂ := h
    have hsq : (ℓ₁ + 1) ^ 2 ≤ ℓ₂ ^ 2 := Nat.pow_le_pow_left hle 2
    have ha_upper : a + 1 ≤ (ℓ₁ + 1) ^ 2 := by
      have : 0 < (ℓ₁ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
      omega
    omega
  · have hle : ℓ₂ + 1 ≤ ℓ₁ := h
    have hsq : (ℓ₂ + 1) ^ 2 ≤ ℓ₁ ^ 2 := Nat.pow_le_pow_left hle 2
    have ha_upper : a + 1 ≤ (ℓ₂ + 1) ^ 2 := by
      have : 0 < (ℓ₂ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
      omega
    omega
end FockSPR
