-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.drop_succ_of_drop_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/311eeed5-c7e0-4b0a-ab69-799d2a785b04

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
theorem _root_.solution {α : Type}
    (literals : List α) (prefixIndex : ℕ)
    (literal : α) (remaining : List α)
    (hdrop : literals.drop prefixIndex = literal :: remaining) :
    literals.drop (prefixIndex + 1) = remaining := by
  have h := congrArg (List.drop 1) hdrop
  simpa [List.drop_drop] using h
end GapCVP.ThreeCNFReduction
