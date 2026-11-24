-- Prove2me | solution 1 for Formalism.NG.globalConcrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:26.058643+00:00
-- url     : https://prove2.me/submissions/8a28cbfc-dceb-4cba-8565-8b25d5e25b91

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GenFin
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_DetTri
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_VccSpan
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalConcreteOf
import Theorems.Thm_Formalism_NG_globalConcrete_of
import Theorems.Thm_Formalism_NG_descent
import Theorems.Thm_Formalism_NG_vccSpan


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
universe u v w
namespace Formalism.NG
theorem _root_.solution : CharacterColumnGlobal := globalConcrete_of descent vccSpan
end Formalism.NG
