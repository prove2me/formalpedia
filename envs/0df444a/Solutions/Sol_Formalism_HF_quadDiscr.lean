-- Prove2me | solution 1 for Formalism.HF.quadDiscr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:27.141559+00:00
-- url     : https://prove2.me/submissions/d13154a9-7a8c-41a7-bd8b-702a600b31c0

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_QuadDiscr
import Theorems.Thm_Formalism_HF_P_quadDiscr_ne_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial Matrix
noncomputable section
namespace Formalism.HF
theorem _root_.solution : Formalism.HF.QuadDiscr := by
  intro K _ _ a x hx hadj hsf h4
  by_cases h1 : a = 1
  · subst h1
    have hx1 : x * x = 1 := by rw [← sq, hx]; simp
    have hbot : x ∈ (⊥ : IntermediateField ℚ K) := by
      rcases mul_self_eq_one_iff.1 hx1 with h | h
      · rw [h]; exact IntermediateField.one_mem _
      · rw [h]; exact IntermediateField.neg_mem _ (IntermediateField.one_mem _)
    have htop : (⊥ : IntermediateField ℚ K) = ⊤ := by
      rw [← hadj, eq_comm]; exact IntermediateField.adjoin_simple_eq_bot_iff.2 hbot
    let e : ℚ ≃ₐ[ℚ] K := (IntermediateField.botEquiv ℚ K).symm.trans
      ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)
    rw [← NumberField.discr_eq_discr_of_algEquiv ℚ e, NumberField.discr_rat]
  · exact Formalism.HF.P.quadDiscr_ne_one K a x hx hadj hsf h4 h1
end Formalism.HF
