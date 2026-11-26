-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminalBlocks_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:02.368802+00:00
-- url     : https://prove2.me/submissions/ab3f2ba5-9364-48ef-a120-1791525aec91

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
    ∀ d ∈ terminalBlocks c r, 0 < d := by
  intro d hd
  exact c.blocks_pos (List.mem_of_mem_drop hd)
end CollatzEndpointTransport.FixedTotal
