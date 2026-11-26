-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedRenyiNumerator_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:20.61069+00:00
-- url     : https://prove2.me/submissions/edef7eba-327c-430d-9f80-0fe3db049cc9

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralMomentCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) (theta : ℝ) :
    0 ≤ fixedRenyiNumerator N s theta := by
  unfold fixedRenyiNumerator
  positivity
end CollatzEndpointTransport.FixedTotal
