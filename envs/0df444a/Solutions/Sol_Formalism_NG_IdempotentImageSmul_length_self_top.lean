-- Prove2me | solution 1 for Formalism.NG.IdempotentImageSmul.length_self_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:40.651953+00:00
-- url     : https://prove2.me/submissions/b5d77cbb-3460-49d3-8fd4-6ef22cb01d50

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentImageSmul
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
namespace Formalism.NG.IdempotentImageSmul
theorem _root_.solution : Module.length O O = ⊤ := by
  by_contra h
  have hfl : IsFiniteLength O O := Module.length_ne_top_iff.mp h
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  haveI : IsArtinianRing O := hfl.2
  exact IsDiscreteValuationRing.not_isField O (IsArtinianRing.isField_of_isDomain O)
end Formalism.NG.IdempotentImageSmul
