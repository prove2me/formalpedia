-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.initialBlocks_append_terminalBlocks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:29:54.762477+00:00
-- url     : https://prove2.me/submissions/0e33fb90-523e-4583-bce9-979f448776f5

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
    {N : ℕ} (c : Composition N) (r : ℕ) :
    initialBlocks c r ++ terminalBlocks c r = c.blocks := by
  exact List.take_append_drop (c.length - r) c.blocks
end CollatzEndpointTransport.FixedTotal
