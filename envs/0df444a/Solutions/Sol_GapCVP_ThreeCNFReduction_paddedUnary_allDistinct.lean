-- Prove2me | solution 1 for GapCVP.ThreeCNFReduction.paddedUnary_allDistinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/4366be8a-9f3c-4d18-9d92-0d4f478cece7

import Mathlib
import Definitions.Def_GapCVP
import Theorems.Thm_P2M_GapCVP_ThreeCNFReduction_paddingVariable__ne_paddingVariable__0fa631a632f4
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
theorem _root_.solution (a : Literal)
    (ha₀ : a.1 ≠ paddingVariable₀)
    (ha₁ : a.1 ≠ paddingVariable₁) :
    allDistinct (paddedUnary a) := by
  simp only [GapCVP.ThreeCNFReduction.allDistinct, decide_eq_true_eq]
  intro clause hclause
  simp only [paddedUnary, List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with h | h | h | h
  all_goals
    subst clause
    exact triple_distinct _ _ _ ha₀ ha₁
      paddingVariable₀_ne_paddingVariable₁
end GapCVP.ThreeCNFReduction
