-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sum_choose_lower_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:44:06.184383+00:00
-- url     : https://prove2.me/submissions/dfb1b7d0-d7ef-4308-80ef-061af30eb3fe

import Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 200000
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (H K : ℕ) :
    (∑ k ∈ Finset.Ico 0 (K + 1), (H.choose k : ℝ)) =
      CollatzEndpointTransport.Terras.lowerBinomialSum H K := by
  simp [CollatzEndpointTransport.Terras.lowerBinomialSum,
    Nat.Ico_zero_eq_range]
end CollatzEndpointTransport.FixedTotal
