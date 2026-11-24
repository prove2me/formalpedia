-- Prove2me | solution 1 for DeletedPrimes.kappaK_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:17.956592+00:00
-- url     : https://prove2.me/submissions/7366268b-bf5a-411e-adf4-f8240a8f79df

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) : 0 < kappaK k α := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  unfold kappaK
  split_ifs
  · exact div_pos (by linarith) (by have : 0 ≤ α ^ 2 / k := by positivity
                                    linarith)
  · exact div_pos (by linarith) (by have : 0 ≤ (1 - α) ^ 2 / k := by positivity
                                    linarith)
end DeletedPrimes
