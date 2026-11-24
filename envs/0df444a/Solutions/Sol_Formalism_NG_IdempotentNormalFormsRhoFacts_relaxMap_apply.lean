-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.relaxMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:57.273982+00:00
-- url     : https://prove2.me/submissions/ce190004-069a-4ce8-83fb-6bac9e77dfe1

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
variable {O C ι : Type*} [CommRing O] [AddCommGroup C] [Module O C]
  {Cw : ι → Type*} [∀ w, AddCommGroup (Cw w)] [∀ w, Module O (Cw w)]
  (what₂ : Finset ι) (res : ∀ w, C →ₗ[O] Cw w) (F F' : ∀ w, Submodule O (Cw w)) (Q : Submodule O C)
namespace Formalism.NG.IdempotentNormalFormsRhoFacts
theorem _root_.solution (x : ↥(Q ⊓ ⨅ w ∈ what₂, (F' w).comap (res w))) (w : what₂) :
    relaxMap what₂ res F F' Q x w =
      Submodule.Quotient.mk ⟨res w.1 x.1, ((mem_sel what₂ res F' Q x.1).mp x.2).2 w.1 w.2⟩ :=
  rfl
end Formalism.NG.IdempotentNormalFormsRhoFacts
