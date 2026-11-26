-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.reverseMomentMajorant_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:34:28.473839+00:00
-- url     : https://prove2.me/submissions/6a9f4690-6482-476e-83e7-b308f75b0f26

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat
open Finset
open scoped NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (theta : ℝ) (k : ℕ) (ks : List ℕ) :
    reverseMomentMajorant theta (k :: ks) =
      (1 + (3 : ℝ≥0) ^ theta * reverseMomentMajorant theta ks) /
        (((2 : ℝ≥0) ^ k) ^ theta) := rfl
end CollatzEndpointTransport.FixedTotal
