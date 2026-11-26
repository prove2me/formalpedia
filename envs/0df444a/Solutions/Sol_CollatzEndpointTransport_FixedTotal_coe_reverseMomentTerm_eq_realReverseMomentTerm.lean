-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.coe_reverseMomentTerm_eq_realReverseMomentTerm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:23.343968+00:00
-- url     : https://prove2.me/submissions/02f5b91e-52e6-49a0-882a-fdb7bcacf23e

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_take_reverse_eq_reverseSpend


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} {N : ℕ} (c : Composition N) {r : ℕ} (hr : 0 < r) :
    (reverseMomentTerm theta c.blocks.reverse (r - 1) : ℝ) =
      realReverseMomentTerm theta c r := by
  unfold reverseMomentTerm realReverseMomentTerm
  rw [Nat.sub_add_cancel hr]
  rw [sum_take_reverse_eq_reverseSpend]
  norm_cast
end CollatzEndpointTransport.FixedTotal
