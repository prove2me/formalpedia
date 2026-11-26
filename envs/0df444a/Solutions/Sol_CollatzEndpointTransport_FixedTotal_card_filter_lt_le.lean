-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_filter_lt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:26:14.820727+00:00
-- url     : https://prove2.me/submissions/2be0b920-489e-46ce-8282-c04c0bb819f5

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_cons
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_syracuseNumeratorList_nil
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_cons
attribute [local simp] CollatzEndpointTransport.FixedTotal.syracuseNumeratorList_nil



set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (S : Finset ℕ) (h : ℕ) :
    (S.filter fun q => q < h).card ≤ h := by
  have hsub :
      S.filter (fun q => q < h) ⊆ Finset.range h := by
    intro q hq
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hq).2
  simpa using Finset.card_le_card hsub
end CollatzEndpointTransport.FixedTotal
