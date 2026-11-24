-- Prove2me | solution 1 for Formalism.L2.Th1.E.unit_at_rules
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:29:32.026291+00:00
-- url     : https://prove2.me/submissions/2ac48333-1deb-4a74-8d26-76f2f92b2746

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_mul
import Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_pow
import Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_of_coeff
import Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_gaussOne
import Theorems.Thm_Formalism_L2_Th1_E_Ser_unitAt_C_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
namespace Formalism.L2.Th1.E
theorem _root_.solution : UnitAtRules := by
  intro K _ _
  exact ⟨fun _ _ _ _ => Ser.unitAt_mul, fun _ n _ hf => Ser.unitAt_pow hf n,
    fun _ _ => Ser.unitAt_of_coeff, fun _ _ => Ser.unitAt_gaussOne,
    fun _ _ _ => Ser.unitAt_C_mul⟩
end Formalism.L2.Th1.E
