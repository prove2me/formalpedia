-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.fixedReverseTermSum_eq_terminalPatterns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:45:59.442412+00:00
-- url     : https://prove2.me/submissions/3c21409d-a7d4-4daa-9021-9e1bf626bf39

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_realReverseMomentTerm_eq_pattern
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sum_by_terminalBlocks


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real NNReal
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    (N s : ℕ) (theta : ℝ) (r : ℕ) :
    fixedReverseTermSum N s theta r =
      ∑ d ∈ terminalPatternImage N s r,
        (terminalFiber N s r d).card *
          realTerminalPatternTerm theta r d := by
  unfold fixedReverseTermSum
  simp_rw [realReverseMomentTerm_eq_pattern]
  exact sum_by_terminalBlocks
    (R := ℝ) (N := N) (s := s) (r := r)
      (realTerminalPatternTerm theta r)
end CollatzEndpointTransport.FixedTotal
