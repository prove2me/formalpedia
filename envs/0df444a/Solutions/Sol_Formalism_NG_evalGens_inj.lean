-- Prove2me | solution 1 for Formalism.NG.evalGens_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:58.686189+00:00
-- url     : https://prove2.me/submissions/4f778d3b-8b23-4ee7-aa50-4e67ff7f154d

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
variable {R O M NN : Type*} [Ring R] [CommRing O] [AddCommGroup M] [Module R M] [Module O M]
  [SMulCommClass R O M] [AddCommGroup NN] [Module R NN] {g : Type} [Fintype g]
namespace Formalism.NG
theorem _root_.solution (n : g → NN) (hspan : Submodule.span R (Set.range n) = ⊤) :
    Function.Injective (fun (φ : NN →ₗ[R] M) (j : g) => φ (n j)) := by
  intro φ ψ h
  exact LinearMap.ext_on_range hspan fun j => congrFun h j
end Formalism.NG
