-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:49:25.519818+00:00
-- url     : https://prove2.me/submissions/ec078ea9-161f-4116-8ad1-5c99757b912f

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
    0 ≤ fixedRenyiMoment N s theta := by
  unfold fixedRenyiMoment fixedRenyiNumerator
  positivity
end CollatzEndpointTransport.FixedTotal
