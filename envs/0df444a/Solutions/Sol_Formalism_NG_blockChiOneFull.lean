-- Prove2me | solution 1 for Formalism.NG.blockChiOneFull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:49:22.212144+00:00
-- url     : https://prove2.me/submissions/f56e1efa-e78a-404c-9ee3-26998ac4b969

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Theorems.Thm_Formalism_NG_blockChiOneFull_of
import Theorems.Thm_Formalism_NG_colKerChiOne


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.NG
universe u₁ u₂ u₃ u₄ u₅ u₆
namespace Formalism.NG
theorem _root_.solution : StatBlockChiOneFull := blockChiOneFull_of colKerChiOne
end Formalism.NG
