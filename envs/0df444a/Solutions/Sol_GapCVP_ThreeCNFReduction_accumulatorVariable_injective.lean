-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.accumulatorVariable_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/946e8282-60db-49f1-bb31-16a5816fe3ee

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
theorem _root_.solution :
    Function.Injective
      (fun p : ℕ × ℕ => accumulatorVariable p.1 p.2) := by
  intro a b h
  apply Encodable.encode_injective
  change 4 * Encodable.encode a + 1 =
    4 * Encodable.encode b + 1 at h
  omega
end GapCVP.ThreeCNFReduction
