-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedSet_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:40:48.079535+00:00
-- url     : https://prove2.me/submissions/ba823085-df53-4664-a496-1a4818e38021

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
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N : ℕ) (hN : 0 < N) :
  fixedSet N 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  have hlen : c.length = 0 := (Finset.mem_filter.mp hc).2
  exact (Nat.ne_of_gt (c.length_pos_of_pos hN)) hlen
end CollatzEndpointTransport.FixedTotal
