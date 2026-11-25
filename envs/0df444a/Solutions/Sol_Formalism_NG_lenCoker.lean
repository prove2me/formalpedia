-- Prove2me | solution 1 for Formalism.NG.lenCoker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:18:32.307982+00:00
-- url     : https://prove2.me/submissions/36b8773a-2f00-4090-a7be-6c9d13bddb54

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Theorems.Thm_Formalism_NG_lenCoker_of_det_ne_zero
import Theorems.Thm_Formalism_NG_lenCoker_of_det_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatLenCoker := by
  intro O _ _ _ ι _ _ A
  by_cases hd : A.det = 0
  · rw [lenCoker_of_det_eq_zero A hd, hd, addVal_zero]
  · exact lenCoker_of_det_ne_zero A hd
end Formalism.NG
