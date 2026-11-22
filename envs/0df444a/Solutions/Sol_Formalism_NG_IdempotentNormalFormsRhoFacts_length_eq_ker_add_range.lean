-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.length_eq_ker_add_range
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:07:04.804595+00:00
-- url     : https://prove2.me/submissions/c57f8b2e-ff5d-4c9a-93dd-7020577d56d8

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
theorem _root_.solution {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (φ : M →ₗ[R] P) :
    Module.length R M =
      Module.length R (LinearMap.ker φ) + Module.length R (LinearMap.range φ) :=
  Module.length_eq_add_of_exact (LinearMap.ker φ).subtype φ.rangeRestrict
    Subtype.val_injective φ.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
end Formalism.NG.IdempotentNormalFormsRhoFacts
