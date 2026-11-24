-- Prove2me | solution 1 for FockSPR.monomial_peak_localization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:08:18.788457+00:00
-- url     : https://prove2.me/submissions/649333f6-ca0d-4cb0-9f55-5139e6be58df

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
theorem _root_.solution {n ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hn : n ∈ freqBlock ℓ) :
    (ℓ : ℝ) < Real.sqrt (n + 1 / 2) ∧
      Real.sqrt (n + 1 / 2) < (ℓ + 1 : ℝ) := by
  simp only [freqBlock, Finset.mem_Icc] at hn
  constructor
  · rw [show (ℓ : ℝ) = Real.sqrt ((ℓ : ℝ) ^ 2) from by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_lt_sqrt (by positivity)
    have : (ℓ : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn.1
    linarith only [this]
  · rw [show (ℓ + 1 : ℝ) = Real.sqrt ((ℓ + 1 : ℝ) ^ 2) from by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_lt_sqrt
      (by linarith only [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    have h1 : n + 1 ≤ (ℓ + 1) ^ 2 := by
      have : 0 < (ℓ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
      omega
    have : (n : ℝ) + 1 ≤ ((ℓ + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h1
    push_cast at this ⊢; linarith only [this]
end FockSPR
