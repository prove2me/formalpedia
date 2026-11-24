-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsRhoFacts.length_pi_rows
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:44.102792+00:00
-- url     : https://prove2.me/submissions/7f23d2b2-f84a-435d-8171-23a2b2efe24a

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
theorem _root_.solution :
    Module.length O ((w : what₂) → (F' w.1 ⧸ (F w.1).comap (F' w.1).subtype)) =
      ∑ w ∈ what₂, Module.length O (F' w ⧸ (F w).comap (F' w).subtype) := by
  rw [Module.length_pi_of_fintype (R := O)
    (fun w : what₂ => (F' w.1 ⧸ (F w.1).comap (F' w.1).subtype))]
  exact Finset.sum_coe_sort what₂ (fun w => Module.length O (F' w ⧸ (F w).comap (F' w).subtype))
end Formalism.NG.IdempotentNormalFormsRhoFacts
