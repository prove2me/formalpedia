-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralReverseTailRatio_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:13.955583+00:00
-- url     : https://prove2.me/submissions/377a6fa4-d094-49e9-9585-17c7dd822848

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ} (hpi1 : pi ≤ 1) :
    0 ≤ centralReverseTailRatio theta pi := by
  unfold centralReverseTailRatio
  exact div_nonneg (sub_nonneg.mpr hpi1)
    (Real.rpow_nonneg (by norm_num) theta)
end CollatzEndpointTransport.FixedTotal
