-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.sourceVariable_ne_accumulatorVariable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/b3644384-d8be-4b59-8176-d9e28eea626d

import Mathlib
import Definitions.Def_GapCVP

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution {T S : ℕ}
    (v : Variable T S) (clauseIndex prefixIndex : ℕ) :
    sourceVariable v ≠ accumulatorVariable clauseIndex prefixIndex := by
  unfold sourceVariable accumulatorVariable
  omega
end GapCVP.ThreeCNFReduction
