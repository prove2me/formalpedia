-- Prove2me | solution 1 for Formalism.L2.Th1.F.taylor_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:00:09.561734+00:00
-- url     : https://prove2.me/submissions/02a4a2ec-d70d-4f84-8090-f142ebed1479

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EndoZInstance
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Theorems.Thm_Formalism_L2_Th1_F_Taylor_taylor0_exp

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
theorem _root_.solution : TaylorExp := fun _ hf h0 => Taylor.taylor0_exp hf h0
end Formalism.L2.Th1.F
