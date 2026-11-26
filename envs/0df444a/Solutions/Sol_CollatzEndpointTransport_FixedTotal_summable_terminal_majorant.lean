-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.summable_terminal_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:41.809407+00:00
-- url     : https://prove2.me/submissions/79501ac4-8d47-43a0-a106-9b9e2f68e763

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseLiftNumerator_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_normalizedReverseLift_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_nil
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseMomentMajorant_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_norm_centralReverseTailRatio_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_shifted_terminal_majorant_eq
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
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ} {r : ℕ}
    (htheta : 0 < theta) (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1)
    (hr : 0 < r) :
    Summable fun n : ℕ =>
      pi ^ r * (1 - pi) ^ n *
        ((n + r - 1).choose (r - 1) : ℝ) *
        realTerminalSpendTerm theta r (n + r) := by
  have hq := norm_centralReverseTailRatio_lt_one htheta hpi0 hpi1
  have hs := summable_choose_mul_geometric_of_norm_lt_one (r - 1) hq
  have hs' : Summable fun n : ℕ =>
      ((n + r - 1).choose (r - 1) : ℝ) *
        centralReverseTailRatio theta pi ^ n := by
    simpa [Nat.add_sub_assoc (by omega : 1 ≤ r)] using hs
  simpa only [shifted_terminal_majorant_eq
    (theta := theta) (pi := pi) hr] using
      hs'.mul_left ((3 : ℝ) ^ (-theta) *
        (((3 : ℝ) ^ theta * pi / (2 : ℝ) ^ theta) ^ r))
end CollatzEndpointTransport.FixedTotal
