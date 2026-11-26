-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.card_terminalFiber_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:43:06.195092+00:00
-- url     : https://prove2.me/submissions/ca7d522b-3a0a-4362-b440-fac81f4f064f

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_fixedSet
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_terminalFiber_le

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped NNReal
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.terminalCompositionDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {N s r : ℕ} (d : List ℕ)
    (hprefixTotal : 0 < N - d.sum) (hprefixLength : 0 < s - r) :
    (terminalFiber N s r d).card ≤
      (N - d.sum - 1).choose (s - r - 1) := by
  calc
    (terminalFiber N s r d).card ≤
        (fixedSet (N - d.sum) (s - r)).card := card_terminalFiber_le d
    _ = (N - d.sum - 1).choose (s - r - 1) :=
      card_fixedSet (N - d.sum) (s - r) hprefixTotal hprefixLength
end CollatzEndpointTransport.FixedTotal
