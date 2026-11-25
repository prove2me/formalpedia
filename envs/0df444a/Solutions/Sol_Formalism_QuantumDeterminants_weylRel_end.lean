-- Prove2me | solution 1 for Formalism.QuantumDeterminants.weylRel_end
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:34:04.511711+00:00
-- url     : https://prove2.me/submissions/e3b12dfd-033c-4d79-8c27-957daaf578df

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRPres
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_WRWeyl
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
import Definitions.Def_Formalism_YangianSpanCharacter_StatementT
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Theorems.Thm_Formalism_QuantumDeterminants_weyl_functional_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.QuantumDeterminants
theorem _root_.solution (l : Fin m) :
    Formalism.YangianSpanCharacter.T.WeylRel (pEnd (E := E) l) (cEnd l) (ciEnd l) := by
  have hw := weyl_functional_holds
  unfold WeylFun at hw
  unfold Formalism.YangianSpanCharacter.T.WeylRel
  refine ⟨?_, ?_, ?_⟩ <;> refine LinearMap.ext fun f => Subtype.ext ?_
  · exact (hw m E l f f.2).1
  · exact (hw m E l f f.2).2.1
  · exact (hw m E l f f.2).2.2.1
end Formalism.QuantumDeterminants
