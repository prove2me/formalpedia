-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedReverseTermSum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:22.993941+00:00
-- url     : https://prove2.me/submissions/7602fd97-49d9-4947-97f0-a6430a8a879c

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_realReverseMomentTerm_nonneg

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) (theta : ℝ) (r : ℕ) :
    0 ≤ fixedReverseTermSum N s theta r := by
  unfold fixedReverseTermSum
  exact sum_nonneg fun c _ => realReverseMomentTerm_nonneg theta c r
end CollatzEndpointTransport.FixedTotal
