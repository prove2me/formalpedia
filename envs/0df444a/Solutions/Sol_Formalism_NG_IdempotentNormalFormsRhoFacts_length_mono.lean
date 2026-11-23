-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.length_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:51.37478+00:00
-- url     : https://prove2.me/submissions/559b236f-bc6b-4049-a8c2-deca5701658f

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange

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
open Formalism.NG.IdempotentNormalFormsRhoFacts
namespace Formalism.NG.IdempotentNormalFormsRhoFacts
theorem _root_.solution {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {A B : Submodule R M}
    (h : A ≤ B) : Module.length R A ≤ Module.length R B :=
  Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
end Formalism.NG.IdempotentNormalFormsRhoFacts
