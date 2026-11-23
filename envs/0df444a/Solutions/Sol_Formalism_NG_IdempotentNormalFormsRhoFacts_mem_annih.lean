-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.mem_annih
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:51.72863+00:00
-- url     : https://prove2.me/submissions/e7f9b9a2-d42b-4115-879c-5872c0333750

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
theorem _root_.solution {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw]
    [AddCommGroup Cs] [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P)
    (U : Submodule O Cs) (c : Cw) : c ∈ annih pr U ↔ ∀ x ∈ U, pr c x = 0 := by
  simp [annih, Submodule.mem_iInf, LinearMap.flip_apply]
end Formalism.NG.IdempotentNormalFormsRhoFacts
