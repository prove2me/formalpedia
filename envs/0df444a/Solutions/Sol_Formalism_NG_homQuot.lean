-- Prove2me | solution 1 for Formalism.NG.homQuot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:18:18.400079+00:00
-- url     : https://prove2.me/submissions/17336e0b-671c-4faf-b386-e91e10b5fd49

import Definitions.Def_Formalism_CharacterColumnKernels_StatementX
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SingleEqSmul
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LenCokerOfDetNeZero
import Theorems.Thm_Formalism_NG_evalGens_mem
import Theorems.Thm_Formalism_NG_evalGens_inj

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
namespace Formalism.NG
theorem _root_.solution : StatHomQuot := by
  intro R O M NN _ _ _ _ _ _ _ _ g _ _ Θ n hspan hrel
  refine ⟨evalGens_mem Θ n hrel, evalGens_inj n hspan, ?_⟩
  exact Module.length_le_of_injective
    (LinearMap.codRestrict (LinearMap.ker (relMap O M Θ)) (evalGens (O := O) (M := M) n)
      (evalGens_mem Θ n hrel))
    fun φ ψ h => evalGens_inj n hspan (congrArg Subtype.val h)
end Formalism.NG
