-- Prove2me | solution 1 for DeletedPrimes.errExp_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:14:59.516264+00:00
-- url     : https://prove2.me/submissions/a1c413c7-061c-4e81-aa7b-312c8c115cdc

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents
import Theorems.Thm_DeletedPrimes_hitExp_le_pos
import Theorems.Thm_DeletedPrimes_hitExp_le_neg
import Theorems.Thm_DeletedPrimes_le_hitExp_u

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α κ τ : ℝ} (hτ0 : 0 ≤ τ) (hτκ : τ ≤ κ) :
    errExp 1 α κ τ = (α - 1) + κ + τ * (1 - α) + min (α * κ) (κ - τ) - α * κ := by
  have hκu : κ = ((1 : ℕ) : ℝ) * κ := by simp
  have hH : hitExp 1 α κ τ = min (α * κ) (κ - τ) := by
    apply le_antisymm
    · apply le_min
      · have h := hitExp_le_neg (α := α) (τ := τ) le_rfl hκu (i := 1) le_rfl
          (by push_cast; linarith)
        push_cast at h
        linarith
      · have h := hitExp_le_pos (α := α) (τ := τ) le_rfl hκu (i := 0) (Nat.zero_le _)
          (by push_cast; linarith)
        push_cast at h
        linarith
    · apply le_hitExp_u le_rfl hκu
      intro i hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · have := le_max_left (κ - τ - ((0 : ℕ) : ℝ) * κ) 0
        have := min_le_right (α * κ) (κ - τ)
        push_cast at *
        linarith
      · have := le_max_right (κ - τ - ((1 : ℕ) : ℝ) * κ) 0
        have := min_le_left (α * κ) (κ - τ)
        push_cast at *
        linarith
  unfold errExp
  rw [hH]
end DeletedPrimes
