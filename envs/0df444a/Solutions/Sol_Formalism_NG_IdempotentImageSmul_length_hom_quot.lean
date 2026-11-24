-- Prove2me | solution 1 for Formalism.NG.IdempotentImageSmul.length_hom_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:54:14.666941+00:00
-- url     : https://prove2.me/submissions/f1d42ede-d019-4f6f-865e-de50a5ead527

import Definitions.Def_Formalism_CharacterColumnKernels_StatementMF
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Theorems.Thm_Formalism_NG_lenKer


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
theorem _root_.solution (a : O) :
    Module.length O ((O ⧸ Ideal.span ({a} : Set O)) →ₗ[O] KO O) = addVal O a := by
  rw [(homQuotEquiv a).length_eq, lenKer O Unit (fun _ _ => a)]
  exact congrArg _ (Matrix.det_unique _)
end Formalism.NG.IdempotentImageSmul
