-- Prove2me | solution 1 for DeletedPrimes.hitExp_le_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:54:34.847438+00:00
-- url     : https://prove2.me/submissions/37a6c2ab-33d0-40f5-83f3-9d34dffc98f3

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
    (ha : 0 ≤ κ - τ - i * u) : hitExp k α κ τ ≤ α * i * u + (κ - τ - i * u) := by
  have h := hitExp_le_term (α := α) (κ := κ) (τ := τ) hi
  rw [term_u hk hκu, max_eq_left ha] at h
  exact h
end DeletedPrimes
