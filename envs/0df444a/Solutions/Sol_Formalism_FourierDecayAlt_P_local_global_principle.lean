-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.local_global_principle
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:35.202813+00:00
-- url     : https://prove2.me/submissions/5a5877d5-7d29-4a98-afb3-d572f6e5d4c4

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_finite_bad
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_mem_of_forall_locAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.S6.LocalGlobal := by
  intro E _ _ _ L hL
  exact ⟨S6x6.finite_bad hL, S6x6.mem_of_forall_locAt hL, S6x6.approx hL⟩
end Formalism.FourierDecayAlt.P
