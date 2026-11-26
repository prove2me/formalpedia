-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.pow_mul_lowerBinomialSum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:24:28.082821+00:00
-- url     : https://prove2.me/submissions/386cae61-bda8-453b-8d5a-97e397a1ca98

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_weightedBinomialSum_eq

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H K : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    x ^ K * (lowerBinomialSum H K : ℝ) ≤ (1 + x) ^ H := by
  calc
    x ^ K * (lowerBinomialSum H K : ℝ) =
        ∑ k ∈ Finset.range (K + 1), x ^ K * (H.choose k : ℝ) := by
          simp [lowerBinomialSum, Nat.cast_sum, Finset.mul_sum]
    _ ≤ ∑ k ∈ Finset.range (K + 1), (H.choose k : ℝ) * x ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkK : k ≤ K := by
        exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hpow : x ^ K ≤ x ^ k :=
        pow_le_pow_of_le_one hx0 hx1 hkK
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (H.choose k))
    _ ≤ ∑ k ∈ Finset.range (H + 1), (H.choose k : ℝ) * x ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.range_mono (Nat.succ_le_succ hKH))
      intro k _ _
      positivity
    _ = (1 + x) ^ H := weightedBinomialSum_eq H x
end CollatzEndpointTransport.Terras
