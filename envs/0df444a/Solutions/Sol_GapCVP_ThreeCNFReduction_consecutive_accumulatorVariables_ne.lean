-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.consecutive_accumulatorVariables_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/39eabb84-1d27-4bf5-9caa-8a87e660a83b

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_accumulatorVariable_injective

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution
    (clauseIndex prefixIndex : ℕ) :
    accumulatorVariable clauseIndex prefixIndex ≠
      accumulatorVariable clauseIndex (prefixIndex + 1) := by
  intro h
  have hp := accumulatorVariable_injective
    (show accumulatorVariable
      (clauseIndex, prefixIndex).1 (clauseIndex, prefixIndex).2 =
      accumulatorVariable
      (clauseIndex, prefixIndex + 1).1
      (clauseIndex, prefixIndex + 1).2 from h)
  have := congrArg Prod.snd hp
  omega
end GapCVP.ThreeCNFReduction
