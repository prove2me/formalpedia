-- Prove2me | solution 1 for Formalism.NG.n5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:18:37.737619+00:00
-- url     : https://prove2.me/submissions/2009f601-acb1-4b1e-b278-7410f5154826

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_GlobalColumn
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_CharacterColumnKernelsOfBlockChiCOfBlockChiOne
import Theorems.Thm_Formalism_NG_character_column_kernels_of_block_chi_c_of_block_chi_one
import Theorems.Thm_Formalism_NG_blockChiCFull
import Theorems.Thm_Formalism_NG_blockChiOneFull


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
namespace Formalism.NG
theorem _root_.solution : characterColumnKernelEqualityForm := character_column_kernels_of_block_chi_c_of_block_chi_one blockChiCFull blockChiOneFull
end Formalism.NG
