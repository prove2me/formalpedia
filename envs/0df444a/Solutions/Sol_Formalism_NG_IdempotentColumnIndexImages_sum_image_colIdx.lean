-- Prove2me | solution 1 for Formalism.NG.IdempotentColumnIndexImages.sum_image_colIdx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:50.057736+00:00
-- url     : https://prove2.me/submissions/6c8502f6-6dff-4b1d-9d00-e002017d306c

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
    (hinj : Function.Injective colIdx) (f : ι' → ℕ∞) :
    ∑ w ∈ (univ : Finset ι).image colIdx, f w = ∑ l : ι, f (colIdx l) :=
  Finset.sum_image fun _ _ _ _ h => hinj h
end Formalism.NG.IdempotentColumnIndexImages
