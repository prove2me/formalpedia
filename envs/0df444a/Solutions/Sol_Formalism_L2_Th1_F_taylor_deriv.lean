-- Prove2me | solution 1 for Formalism.L2.Th1.F.taylor_deriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:00:14.611116+00:00
-- url     : https://prove2.me/submissions/9dafa813-6178-4ef2-9d1b-2c0d31736a92

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_deriv
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_rescale
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
namespace Formalism.L2.Th1.F
theorem _root_.solution : TaylorDeriv :=
  ⟨fun f _ => Taylor.taylor0_deriv f, fun _ a hf => Taylor.taylor0_rescale a hf,
    fun _ _ hf hg h => Taylor.taylor0_inj hf hg h⟩
end Formalism.L2.Th1.F
