-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedCriticalNumerator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:44.795674+00:00
-- url     : https://prove2.me/submissions/ab5d35d2-288c-4f42-bb81-c7eb3dd6226a

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
import Mathlib.Algebra.Order.Chebyshev
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_injOn_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_residueFibers_critical_bound
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



set_option autoImplicit false
set_option maxHeartbeats 2000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.compositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) :
    fixedCriticalNumerator N s ≤
      4 * ∑ c ∈ fixedSet N s,
        Real.sqrt (3 ^ s + syracuseNumerator c) := by
  have hm : 0 < 3 ^ s := pow_pos (by norm_num) _
  simpa [fixedCriticalNumerator, fixedFiberCard] using
    residueFibers_critical_bound
      (fixedSet N s) syracuseNumerator (3 ^ s) hm
      (syracuseNumerator_injOn_fixedSet N s)
end CollatzEndpointTransport.FixedTotal
