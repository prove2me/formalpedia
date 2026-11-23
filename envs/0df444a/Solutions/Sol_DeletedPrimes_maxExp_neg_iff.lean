-- Prove2me | solution 1 for DeletedPrimes.maxExp_neg_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:47.803572+00:00
-- url     : https://prove2.me/submissions/a721a469-265b-4da6-a5db-f0be7817380e

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    maxExp k α κ < 0 ↔ κ < kappaK k α := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  unfold maxExp kappaK
  split_ifs with hα
  · have hA : 0 ≤ α ^ 2 / k := by positivity
    rw [lt_div_iff₀ (by linarith)]
    constructor <;> intro h <;> linarith
  · have hA : 0 ≤ (1 - α) ^ 2 / k := by positivity
    rw [lt_div_iff₀ (by linarith)]
    constructor <;> intro h <;> linarith
end DeletedPrimes
