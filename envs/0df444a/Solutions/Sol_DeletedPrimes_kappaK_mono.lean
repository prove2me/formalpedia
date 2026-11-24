-- Prove2me | solution 1 for DeletedPrimes.kappaK_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:16:12.668804+00:00
-- url     : https://prove2.me/submissions/71c13501-5293-451f-879c-28f59059149b

import Mathlib
import Definitions.Def_DeletedPrimes_Exponents

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {k k' : ℕ} (hk : 1 ≤ k) (hkk' : k ≤ k') :
    kappaK k α ≤ kappaK k' α := by
  have hkpos : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hkk : (k : ℝ) ≤ k' := by exact_mod_cast hkk'
  have hk'pos : (0 : ℝ) < k' := lt_of_lt_of_le hkpos hkk
  unfold kappaK
  split_ifs
  · have hA : α ^ 2 / k' ≤ α ^ 2 / k := div_le_div_of_nonneg_left (sq_nonneg α) hkpos hkk
    have hA' : 0 ≤ α ^ 2 / k' := by positivity
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
  · have hA : (1 - α) ^ 2 / k' ≤ (1 - α) ^ 2 / k :=
      div_le_div_of_nonneg_left (sq_nonneg _) hkpos hkk
    have hA' : 0 ≤ (1 - α) ^ 2 / k' := by positivity
    exact div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
end DeletedPrimes
