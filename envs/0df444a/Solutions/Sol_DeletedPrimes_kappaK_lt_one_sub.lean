-- Prove2me | solution 1 for DeletedPrimes.kappaK_lt_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:53:20.847575+00:00
-- url     : https://prove2.me/submissions/b4f690e4-b8cf-427d-adbe-1170847425e1

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {k : ℕ} (hk : 1 ≤ k) {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    kappaK k α < 1 - α := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  unfold kappaK
  split_ifs with hα
  · have hA : 0 < α ^ 2 / k := by positivity
    exact div_lt_self (by linarith) (by linarith)
  · have hA : 0 < (1 - α) ^ 2 / k := by
      have : 0 < 1 - α := by linarith
      positivity
    exact div_lt_self (by linarith) (by linarith)
end DeletedPrimes
