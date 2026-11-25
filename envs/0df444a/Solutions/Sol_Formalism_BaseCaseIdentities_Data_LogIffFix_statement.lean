-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.LogIffFix_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:06:39.278495+00:00
-- url     : https://prove2.me/submissions/831430bd-82ea-4878-b873-5ac74e13b80c

import Definitions.Def_Formalism_FrobeniusBaseCase_StatementFix
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_BaseCaseFalseGeneralHolds
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_FixAll
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_logSum
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_PsiPartial
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_opIsLimit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
open Formalism.BaseCaseIdentities.Data
variable {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : D.LogIffFix := by
  intro t ht
  constructor
  · intro h
    funext b
    ext A
    rw [D.opIsLimit t ht b A A.degree le_rfl, coeff_PsiPartial]
    have := h b A A.degree le_rfl
    rw [map_add, coeff_logSum] at this
    linear_combination -this
  · intro h b A N hN
    have := D.opIsLimit t ht b A N hN
    rw [h, coeff_PsiPartial] at this
    rw [map_add, coeff_logSum]
    linear_combination this
end Formalism.BaseCaseIdentities.Data
