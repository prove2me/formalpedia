-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminalBlocks_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:29:46.205801+00:00
-- url     : https://prove2.me/submissions/0045ac42-cc02-47c9-a8f5-b67a47df424c

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
theorem _root_.solution
    {N : ℕ} (c : Composition N) {r : ℕ} (hr : r ≤ c.length) :
    (terminalBlocks c r).length = r := by
  unfold terminalBlocks
  rw [List.length_drop]
  change r ≤ c.blocks.length at hr
  change c.blocks.length - (c.blocks.length - r) = r
  omega
end CollatzEndpointTransport.FixedTotal
