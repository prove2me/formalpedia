-- Prove2me | solution 1 for FockSPR.fockNorm_decomposes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:14:29.986409+00:00
-- url     : https://prove2.me/submissions/9fccd601-bb44-4415-8bf3-26b514a4accf

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
section
@[expose] public section
open Finset Nat Real MeasureTheory
noncomputable section
namespace FockSPR
private lemma freqBlock_unique {n ℓ₁ ℓ₂ : ℕ}
    (h1 : n ∈ freqBlock ℓ₁) (h2 : n ∈ freqBlock ℓ₂) : ℓ₁ = ℓ₂ := by
  simp only [freqBlock, Finset.mem_Icc] at h1 h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hsq : (ℓ₁ + 1) ^ 2 ≤ ℓ₂ ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hpos : 0 < (ℓ₁ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
    omega
  · have hsq : (ℓ₂ + 1) ^ 2 ≤ ℓ₁ ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hpos : 0 < (ℓ₂ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
    omega
private lemma mem_freqBlock_sqrt (n : ℕ) : n ∈ freqBlock (Nat.sqrt n) := by
  simp only [freqBlock, Finset.mem_Icc]
  exact ⟨by have := Nat.sqrt_le n; linarith only [this],
         by have h1 := Nat.lt_succ_sqrt' n; simp only [Nat.succ_eq_add_one] at h1; omega⟩
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution {D : ℕ} (a : Fin D → ℂ) :
    fockNormSq a = ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D),
      ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ) else 0 := by
  unfold fockNormSq
  rw [← Finset.sum_comm]
  congr 1; ext k
  have hk_mem : (k.val + 1) ∈ freqBlock (Nat.sqrt (k.val + 1)) :=
    mem_freqBlock_sqrt _
  have hℓ_mem : Nat.sqrt (k.val + 1) ∈ Finset.Icc 1 (maxBlockIndex D) := by
    simp only [maxBlockIndex, Finset.mem_Icc]
    exact ⟨Nat.sqrt_pos.mpr (by omega), Nat.sqrt_le_sqrt (by omega)⟩
  rw [Finset.sum_eq_single_of_mem _ hℓ_mem]
  · simp [hk_mem]
  · intro b _ hbne
    have : (k.val + 1) ∉ freqBlock b :=
      fun hmem => hbne (freqBlock_unique hmem hk_mem)
    simp [this]
end FockSPR
