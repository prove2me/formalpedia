-- Prove2me | solution 1 for FockSPR.freq_support_localPoly_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:41.995796+00:00
-- url     : https://prove2.me/submissions/c9c750a5-401d-481e-8095-e665285dfda7

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
theorem _root_.solution {M j : ℕ} (_hM : 1 ≤ M) (hj : M + 1 ≤ j) :
    ∀ n ∈ freqBlock ℓ,
      ℓ ∈ Finset.Icc (max 1 (j - M)) (j + M) → (j - M) ^ 2 ≤ n := by
  intro n hn hℓ
  simp only [freqBlock, Finset.mem_Icc] at hn hℓ
  calc (j - M) ^ 2 ≤ ℓ ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ ≤ n := hn.1
end FockSPR
