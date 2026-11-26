-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.binomialAnnulus_index_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:44:44.393823+00:00
-- url     : https://prove2.me/submissions/9f334f67-58d3-45c6-9ac0-a74c7545c52d

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_binomialCenterDistance_le
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
    binomialCenterDistance H k / binomialAnnulusWidth H ∈
      Finset.range (H + 1) := by
  rw [Finset.mem_range]
  have hkH : k ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hdH := binomialCenterDistance_le hkH
  have hW : 0 < binomialAnnulusWidth H := binomialAnnulusWidth_pos H
  have hdiv : binomialCenterDistance H k / binomialAnnulusWidth H ≤
      binomialCenterDistance H k := Nat.div_le_self _ _
  omega
end CollatzEndpointTransport.FixedTotal
