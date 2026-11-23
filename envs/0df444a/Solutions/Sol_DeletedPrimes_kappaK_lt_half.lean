-- Prove2me | solution 1 for DeletedPrimes.kappaK_lt_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:48:26.471617+00:00
-- url     : https://prove2.me/submissions/ebb73e9c-8805-4537-85c2-aea4606a2e96

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    kappaK k α < 1 / 2 := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  unfold kappaK
  split_ifs with hα
  · have hA : 0 < α ^ 2 / k := by positivity
    rw [div_lt_iff₀ (by linarith)]
    linarith
  · push Not at hα
    have hA : 0 ≤ (1 - α) ^ 2 / k := by positivity
    rw [div_lt_iff₀ (by linarith)]
    linarith
end DeletedPrimes
