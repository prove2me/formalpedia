-- Prove2me | solution 1 for Formalism.NG.evalGens_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:09:33.175935+00:00
-- url     : https://prove2.me/submissions/613fc3bb-3387-4433-bd35-1b8097000182

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
theorem _root_.solution (Θ : Matrix g g R) (n : g → NN) (hrel : ∀ i, ∑ j, Θ i j • n j = 0)
    (φ : NN →ₗ[R] M) : (fun j => φ (n j)) ∈ LinearMap.ker (relMap O M Θ) := by
  classical
  rw [LinearMap.mem_ker]
  funext i
  rw [relMap_apply', Pi.zero_apply]
  simp_rw [← LinearMap.map_smul]
  rw [← map_sum, hrel i, map_zero]
end Formalism.NG
