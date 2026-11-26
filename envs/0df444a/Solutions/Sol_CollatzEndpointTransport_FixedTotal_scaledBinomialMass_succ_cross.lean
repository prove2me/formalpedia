-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.scaledBinomialMass_succ_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:41.242508+00:00
-- url     : https://prove2.me/submissions/2b1a3933-f253-428e-81a4-2284015c6fb3

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
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {n k j : ℕ} (hj : j < n) :
    scaledBinomialMass n k (j + 1) * ((j + 1) * (n - k)) =
      scaledBinomialMass n k j * ((n - j) * k) := by
  have hsub : n - j = (n - (j + 1)) + 1 := by omega
  have hchoose := Nat.choose_succ_right_eq n j
  unfold scaledBinomialMass
  calc
    n.choose (j + 1) * k ^ (j + 1) * (n - k) ^ (n - (j + 1)) *
          ((j + 1) * (n - k)) =
        (n.choose (j + 1) * (j + 1)) *
          (k ^ j * k) * ((n - k) ^ (n - (j + 1)) * (n - k)) := by
            rw [pow_succ]
            ring
    _ = (n.choose j * (n - j)) *
          (k ^ j * k) * ((n - k) ^ (n - (j + 1)) * (n - k)) := by
            rw [hchoose]
    _ = n.choose j * k ^ j * (n - k) ^ (n - j) * ((n - j) * k) := by
            rw [hsub, pow_succ]
            ring
end CollatzEndpointTransport.FixedTotal
