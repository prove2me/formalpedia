-- Prove2me | solution 1 for CollatzEndpointTransport.Terras.lowerBinomialSum_le_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:14.254605+00:00
-- url     : https://prove2.me/submissions/cfa62261-5a19-4bb3-90b7-f03684423738

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Theorems.Thm_CollatzEndpointTransport_Terras_pow_mul_lowerBinomialSum_le

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.Terras
open Nat Finset
namespace CollatzEndpointTransport.Terras
theorem _root_.solution
    {H K : ℕ} {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hKH : K ≤ H) :
    (lowerBinomialSum H K : ℝ) ≤ (1 + x) ^ H / x ^ K := by
  apply (le_div_iff₀ (pow_pos hx0 K)).2
  simpa [mul_comm] using
    pow_mul_lowerBinomialSum_le (H := H) (K := K) (x := x) hx0.le hx1 hKH
end CollatzEndpointTransport.Terras
