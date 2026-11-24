-- Prove2me | solution 1 for DeletedPrimes.argmaxExp_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:02:57.914976+00:00
-- url     : https://prove2.me/submissions/85728de5-295c-4653-9f29-fae7e7c6351b

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α κ : ℝ} (h0 : 0 < α) (h1 : α < 1) (hκ : 0 ≤ κ) :
    argmaxExp k α κ ∈ Set.Icc 0 κ := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold argmaxExp
  split_ifs
  · constructor
    · have : α * κ / k ≤ κ := by
        rw [div_le_iff₀ hkpos]; nlinarith
      linarith
    · have : 0 ≤ α * κ / k := by positivity
      linarith
  · constructor
    · exact div_nonneg (mul_nonneg hκ (by linarith)) hkpos.le
    · rw [div_le_iff₀ hkpos]; nlinarith
end DeletedPrimes
