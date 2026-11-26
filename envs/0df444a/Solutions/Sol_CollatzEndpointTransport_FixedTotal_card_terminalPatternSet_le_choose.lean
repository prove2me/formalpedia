-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_terminalPatternSet_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:26.246786+00:00
-- url     : https://prove2.me/submissions/9b8b3d11-0d80-4323-bb93-68d5cbef8d34

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_terminalPatternSet_le

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s r D : ℕ} (hr : r ≤ s) (hD : 0 < D) (hr0 : 0 < r) :
    (terminalPatternSet N s r D).card ≤ (D - 1).choose (r - 1) := by
  calc
    (terminalPatternSet N s r D).card ≤ (fixedSet D r).card :=
      card_terminalPatternSet_le hr
    _ = (D - 1).choose (r - 1) := card_fixedSet D r hD hr0
end CollatzEndpointTransport.FixedTotal
