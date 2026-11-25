-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RelativeIndexFlags.ratio_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:47:42.918454+00:00
-- url     : https://prove2.me/submissions/1ab9a0ed-eec9-4071-9454-b162801a93a8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_RelativeIndexFlags_RelIndexInfRightNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RelativeIndexFlags
variable {G : Type*} [Group G]
namespace Formalism.L2.SG.Pf.RelativeIndexFlags
theorem _root_.solution (φ : G ≃* G) (A S : Subgroup G) :
    ratio (A.map φ.toMonoidHom) (S.map φ.toMonoidHom) = ratio A S := by
  unfold ratio
  rw [Subgroup.relIndex_map_map_of_injective _ _ φ.injective,
    Subgroup.relIndex_map_map_of_injective _ _ φ.injective]
end Formalism.L2.SG.Pf.RelativeIndexFlags
