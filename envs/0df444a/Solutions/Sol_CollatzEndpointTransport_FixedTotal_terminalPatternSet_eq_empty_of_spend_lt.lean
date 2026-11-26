-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.terminalPatternSet_eq_empty_of_spend_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:39:00.1928+00:00
-- url     : https://prove2.me/submissions/8bc7e52c-2011-4330-84ec-84262a9c39c7

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_terminalPatternSet_spend_bounds

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s r D : ℕ} (hrs : r ≤ s) (hDr : D < r) :
    terminalPatternSet N s r D = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro d hd
  have hbounds := terminalPatternSet_spend_bounds hrs hd
  omega
end CollatzEndpointTransport.FixedTotal
