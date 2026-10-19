-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.paddedBinary_allDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/0fc00bd8-72de-4e3a-b54a-b396ca151010

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_GapCVP_ThreeCNFReduction_triple_distinct

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open StateTransition (EvalsToInTime)
open GapCVP
open GapCVP.TraceGolf (oneStep rebound)
open GapCVP.ThreeCNFReduction
open GapCVP.CL
namespace GapCVP.ThreeCNFReduction
theorem _root_.solution (a b : Literal)
    (hab : a.1 ≠ b.1)
    (ha : a.1 ≠ paddingVariable₀)
    (hb : b.1 ≠ paddingVariable₀) :
    allDistinct (paddedBinary a b) := by
  simp only [GapCVP.ThreeCNFReduction.allDistinct, decide_eq_true_eq]
  intro clause hclause
  simp only [paddedBinary, List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with h | h
  · subst clause
    exact triple_distinct _ _ _ hab ha hb
  · subst clause
    exact triple_distinct _ _ _ hab ha hb
end GapCVP.ThreeCNFReduction
