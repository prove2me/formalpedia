-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.length_ker_relaxMap_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:40:52.907961+00:00
-- url     : https://prove2.me/submissions/fe061827-fa95-44b4-ac07-acb1f00eeaec

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_length_mono
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_mem_of_relaxMap

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
variable {O C ι : Type*} [CommRing O] [AddCommGroup C] [Module O C]
  {Cw : ι → Type*} [∀ w, AddCommGroup (Cw w)] [∀ w, Module O (Cw w)]
  (what₂ : Finset ι) (res : ∀ w, C →ₗ[O] Cw w) (F F' : ∀ w, Submodule O (Cw w)) (Q : Submodule O C)
namespace Formalism.NG.IdempotentNormalFormsRhoFacts
theorem _root_.solution :
    Module.length O (LinearMap.ker (relaxMap what₂ res F F' Q)) ≤
      Module.length O ↥(Q ⊓ ⨅ w ∈ what₂, (F w).comap (res w)) := by
  rw [(Submodule.equivMapOfInjective _ (Submodule.injective_subtype _)
    (LinearMap.ker (relaxMap what₂ res F F' Q))).length_eq]
  apply length_mono
  rintro _ ⟨x, hx, rfl⟩
  exact mem_of_relaxMap what₂ res F F' Q x (LinearMap.mem_ker.mp hx)
end Formalism.NG.IdempotentNormalFormsRhoFacts
