-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.threeCNFSatisfiable_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/fe17ee8c-cfb2-458c-88f5-fec63fafd157

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
theorem _root_.solution (formula : ThreeCNF) :
    threeCNFSatisfiable formula ↔
      allDistinct formula ∧
        ∃ assignment : ℕ → Bool, satisfies assignment formula := by
  simp only [GapCVP.threeCNFSatisfiable, GapCVP.ThreeCNFReduction.allDistinct, GapCVP.ThreeCNFReduction.satisfies, decide_eq_true_eq]
end GapCVP.ThreeCNFReduction
