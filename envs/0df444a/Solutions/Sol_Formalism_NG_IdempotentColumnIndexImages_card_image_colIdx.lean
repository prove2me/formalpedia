-- Prove2me | solution 1 for Formalism.NG.IdempotentColumnIndexImages.card_image_colIdx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:49.968975+00:00
-- url     : https://prove2.me/submissions/a4c21702-fd36-4dd4-9250-b7bf7e17d736

import Definitions.Def_Formalism_CharacterColumnKernels_CharacterColumnKernelEqualityForm
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockRhoFull
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerSmulLe
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneTriv
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_ColKerChiOne
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_BlockChiOneFullOf

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
open Formalism.NG.IdempotentColumnIndexImages
namespace Formalism.NG.IdempotentColumnIndexImages
theorem _root_.solution {ι ι' : Type*} [Fintype ι] [DecidableEq ι'] (colIdx : ι → ι')
    (hinj : Function.Injective colIdx) :
    (((univ : Finset ι).image colIdx).card : ℕ∞) = (Fintype.card ι : ℕ∞) := by
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
end Formalism.NG.IdempotentColumnIndexImages
