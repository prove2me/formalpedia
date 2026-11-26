-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSet_card_le_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:49.757003+00:00
-- url     : https://prove2.me/submissions/6f2168cb-01ed-45e6-a1bc-c8e76a8c7e67

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
    (N s : ℕ) :
    (fixedSet N s).card ≤ 2 ^ N := by
  calc
    (fixedSet N s).card ≤ Fintype.card (Composition N) :=
      Finset.card_le_univ _
    _ = 2 ^ (N - 1) := composition_card N
    _ ≤ 2 ^ N := pow_le_pow_right' (by norm_num : (1 : ℕ) ≤ 2)
      (Nat.sub_le N 1)
end CollatzEndpointTransport.FixedTotal
