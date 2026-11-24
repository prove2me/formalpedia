-- Prove2me | solution 1 for Formalism.NG.globalModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:41.879921+00:00
-- url     : https://prove2.me/submissions/280ec120-6096-4274-8100-a3d76ed9ddce

import Definitions.Def_Formalism_CharacterColumnKernels_StatGlobalModule
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CupKillAdm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalModuleOf
import Theorems.Thm_Formalism_NG_globalModule_of
import Theorems.Thm_Formalism_NG_finPres


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.NG
universe u v w x
namespace Formalism.NG
theorem _root_.solution : StatGlobalModule := globalModule_of finPres
end Formalism.NG
