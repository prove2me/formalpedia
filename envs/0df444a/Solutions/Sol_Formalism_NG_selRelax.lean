-- Prove2me | solution 1 for Formalism.NG.selRelax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:54:10.526919+00:00
-- url     : https://prove2.me/submissions/2d08e02d-02c7-487c-ae9d-624ec3d2de84

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_eq_ker_add_range
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_ker_relaxMap_le
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_pi_rows

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
namespace Formalism.NG
theorem _root_.solution : StatSelRelax := by
  intro O C ι _ _ _ what₂ Cw _ _ res F F' Q _
  rw [IdempotentNormalFormsRhoFacts.length_eq_ker_add_range (IdempotentNormalFormsRhoFacts.relaxMap what₂ res F F' Q), ← IdempotentNormalFormsRhoFacts.length_pi_rows]
  gcongr
  · exact IdempotentNormalFormsRhoFacts.length_ker_relaxMap_le what₂ res F F' Q
  · exact Module.length_le_of_injective (Submodule.subtype _) Subtype.val_injective
end Formalism.NG
