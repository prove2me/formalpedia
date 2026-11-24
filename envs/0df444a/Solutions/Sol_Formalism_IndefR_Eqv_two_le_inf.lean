-- Prove2me | solution 1 for Formalism.IndefR.Eqv.two_le_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:21.335126+00:00
-- url     : https://prove2.me/submissions/d5c5dfce-b32e-4f6b-8da5-adb479fcac71

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym
import Theorems.Thm_P2M_Formalism_IndefR_Eqv_natCast_lt_inf__24812f2382ad

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IndefR Formalism.IndefR.Eqv
open scoped ContDiff
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.IndefR.Eqv
theorem _root_.solution : minSmoothness ℝ 2 ≤ ∞ := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact_mod_cast (natCast_lt_inf' 2).le
end Formalism.IndefR.Eqv
