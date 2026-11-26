-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_terminalPatternSet_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:51.041802+00:00
-- url     : https://prove2.me/submissions/3b977414-bb1c-4fc0-8e19-03d97e32d72e

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedBlockSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_subset_fixedBlockSet

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s r D : ℕ} (hr : r ≤ s) :
    (terminalPatternSet N s r D).card ≤ (fixedSet D r).card := by
  calc
    (terminalPatternSet N s r D).card ≤ (fixedBlockSet D r).card :=
      Finset.card_le_card (terminalPatternSet_subset_fixedBlockSet hr)
    _ = (fixedSet D r).card := card_fixedBlockSet D r
end CollatzEndpointTransport.FixedTotal
