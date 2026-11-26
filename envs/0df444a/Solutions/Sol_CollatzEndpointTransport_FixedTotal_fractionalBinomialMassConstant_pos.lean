-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fractionalBinomialMassConstant_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:07:33.545636+00:00
-- url     : https://prove2.me/submissions/62a17c1a-3b5f-412a-87d1-82514712efcd

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    0 < fractionalBinomialMassConstant theta := by
  unfold fractionalBinomialMassConstant
  have hq : Real.exp (-2 * (1 - theta)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  positivity
end CollatzEndpointTransport.FixedTotal
