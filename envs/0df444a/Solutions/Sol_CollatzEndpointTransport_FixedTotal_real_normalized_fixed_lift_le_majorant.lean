-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.real_normalized_fixed_lift_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:08.812835+00:00
-- url     : https://prove2.me/submissions/ae0f372c-8318-492b-9af3-a55fe71e08d7

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalized_fixed_lift_rpow_le_majorant
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne


attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseLiftNumerator_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.normalizedReverseLift_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s : ℕ} {theta : ℝ}
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1)
    (c : Composition N) (hc : c ∈ fixedSet N s) :
    (((((3 ^ s + syracuseNumerator c : ℕ) : ℝ) /
          (2 : ℝ) ^ N)) ^ theta) ≤
      realReverseMajorant theta c := by
  have hlen : c.length = s := (Finset.mem_filter.mp hc).2
  have h := normalized_fixed_lift_rpow_le_majorant
    c htheta0 htheta1
  have hcast :
      (((((3 ^ c.length + syracuseNumerator c : ℕ) : ℝ≥0) /
          ((2 : ℝ≥0) ^ N)) ^ theta : ℝ≥0) : ℝ) ≤
        (reverseMomentMajorant theta c.blocks.reverse : ℝ) := by
    exact_mod_cast h
  simpa [realReverseMajorant, hlen, Nat.cast_add, Nat.cast_pow] using hcast
end CollatzEndpointTransport.FixedTotal
