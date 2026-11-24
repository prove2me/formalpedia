-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.mem_of_relaxMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:28.641623+00:00
-- url     : https://prove2.me/submissions/ac1bdac8-0327-49e7-bb49-a6cff92d04b3

import Definitions.Def_Formalism_CharacterColumnKernels_StatementRho
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEqKerAddRange
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsRhoFacts_relaxMap_apply

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
theorem _root_.solution (x : ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w)))
    (hx : relaxMap what₂ res F F' Q x = 0) : x.1 ∈ Q ⊓ ⨅ w ∈ what₂, (F w).comap (res w) := by
  refine (mem_sel what₂ res F Q x.1).mpr ⟨((mem_sel what₂ res F' Q x.1).mp x.2).1, fun w hw => ?_⟩
  have h0 := congrFun hx ⟨w, hw⟩
  rw [relaxMap_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h0
  exact h0
end Formalism.NG.IdempotentNormalFormsRhoFacts
