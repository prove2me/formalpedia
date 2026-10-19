-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.triple_distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/5cb6a40d-8217-42c2-9e9a-ab1efa6d906e

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
theorem _root_.solution (a b c : Literal)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1) :
    clauseHasDistinctVariables (triple a b c) := by
  simp only [GapCVP.clauseHasDistinctVariables, decide_eq_true_eq]
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [triple]
end GapCVP.ThreeCNFReduction
