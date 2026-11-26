-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.mem_binomialAnnulus_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:37.474979+00:00
-- url     : https://prove2.me/submissions/b00fc220-8f69-4e64-9cc5-75fd11204739

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialAnnulusWidth_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {H k : ℕ} (hk : k ∈ Finset.range (H + 1)) :
    k ∈ binomialAnnulus H
      (binomialCenterDistance H k / binomialAnnulusWidth H) := by
  rw [binomialAnnulus, Finset.mem_filter]
  refine ⟨hk, ?_⟩
  let d := binomialCenterDistance H k
  let W := binomialAnnulusWidth H
  have hW : 0 < W := binomialAnnulusWidth_pos H
  constructor
  · exact Nat.div_mul_le_self d W
  · exact (Nat.div_lt_iff_lt_mul hW).mp (Nat.lt_succ_self (d / W))
end CollatzEndpointTransport.FixedTotal
