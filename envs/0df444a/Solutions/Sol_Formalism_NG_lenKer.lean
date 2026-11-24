-- Prove2me | solution 1 for Formalism.NG.lenKer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:40:57.959092+00:00
-- url     : https://prove2.me/submissions/2ff23c30-49e7-4e1a-8241-dfd401cb7a72

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_ker_of_det_ne_zero
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_ker_of_det_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
open IdempotentNormalFormsLenFacts
namespace Formalism.NG
theorem _root_.solution : StatLenKer := by
  intro O _ _ _ ι _ _ A
  by_cases hd : A.det = 0
  · rw [length_ker_of_det_eq_zero A hd, hd, addVal_zero]
  · exact length_ker_of_det_ne_zero A hd
end Formalism.NG
