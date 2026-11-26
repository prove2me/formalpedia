-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedRenyiNumerator_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:49.805655+00:00
-- url     : https://prove2.me/submissions/157d6d16-73f9-4271-b226-de247b58bd9e

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_residueFibers_renyi_bound
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_blocks
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_prependOne_length
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_injOn_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumerator_prependOne
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.increaseFirst_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_blocks
attribute [local simp] CollatzEndpointTransport.FixedTotal.prependOne_length
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumerator_prependOne



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralMomentCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1) :
    fixedRenyiNumerator N s theta ≤
      4 * fixedLiftMoment N s theta := by
  have hm : 0 < 3 ^ s := pow_pos (by norm_num) _
  simpa [fixedRenyiNumerator, fixedLiftMoment, fixedFiberCard,
    Nat.cast_pow] using
    residueFibers_renyi_bound
      (fixedSet N s) syracuseNumerator (3 ^ s)
      htheta0 htheta1 hm (syracuseNumerator_injOn_fixedSet N s)
end CollatzEndpointTransport.FixedTotal
