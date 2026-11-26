-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminalPatternSet_spend_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:42:13.223741+00:00
-- url     : https://prove2.me/submissions/10e256f0-8916-4695-9508-031f46d24572

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_reverseSpend_lt_of_lt_length

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s r D : ℕ} (hrs : r < s)
    {d : List ℕ} (hd : d ∈ terminalPatternSet N s r D) :
    D < N := by
  rcases Finset.mem_filter.mp hd with ⟨hdImage, hdSum⟩
  rcases Finset.mem_image.mp hdImage with ⟨c, hc, hdc⟩
  have hcLength : c.length = s := (Finset.mem_filter.mp hc).2
  have hspend : reverseSpend c r = D := by
    unfold reverseSpend
    rw [hdc, hdSum]
  rw [← hspend]
  exact reverseSpend_lt_of_lt_length c (by omega)
end CollatzEndpointTransport.FixedTotal
