-- Prove2me | solution 1 for Formalism.IndefR.Eqv.inf_add_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:21.260785+00:00
-- url     : https://prove2.me/submissions/0878571e-20fd-427f-8b87-494c8db181d0

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_IterSymmR
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_SobSym

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
theorem _root_.solution (m : ℕ) : (∞ : WithTop ℕ∞) + (m : WithTop ℕ∞) ≤ ∞ := by
  first
    | (rw [(WithTop.coe_natCast m).symm, ← WithTop.coe_add, top_add])
    | simp
    | (norm_cast; simp)
end Formalism.IndefR.Eqv
