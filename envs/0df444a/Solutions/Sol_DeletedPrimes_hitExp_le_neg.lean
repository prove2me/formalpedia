-- Prove2me | solution 1 for DeletedPrimes.hitExp_le_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:54:42.759808+00:00
-- url     : https://prove2.me/submissions/bf56b12e-8450-458d-87aa-3d5d04002f1d

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
import Theorems.Thm_DeletedPrimes_hitExp_le_term
import Theorems.Thm_DeletedPrimes_term_u

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α κ u τ : ℝ} (hκu : κ = k * u) {i : ℕ} (hi : i ≤ k)
    (ha : κ - τ - i * u ≤ 0) : hitExp k α κ τ ≤ α * i * u := by
  have h := hitExp_le_term (α := α) (κ := κ) (τ := τ) hi
  rw [term_u hk hκu, max_eq_right ha, add_zero] at h
  exact h
end DeletedPrimes
