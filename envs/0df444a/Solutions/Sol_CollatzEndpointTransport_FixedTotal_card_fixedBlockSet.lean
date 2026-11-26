-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_fixedBlockSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:42.475829+00:00
-- url     : https://prove2.me/submissions/b519e91b-e927-421e-8a95-85e24781c247

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
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution (D r : ℕ) :
    (fixedBlockSet D r).card = (fixedSet D r).card := by
  unfold fixedBlockSet
  rw [Finset.card_image_of_injective]
  intro c₁ c₂ h
  apply Composition.ext
  exact h
end CollatzEndpointTransport.FixedTotal
