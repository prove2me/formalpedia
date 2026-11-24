-- Prove2me | solution 1 for Formalism.L2.G.wU_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:24.756302+00:00
-- url     : https://prove2.me/submissions/7c6ae354-f241-46ef-a1f2-0c0185054f78

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_ExistsSqEqIntCast
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_AlgebraMapFinite
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_JOInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G
open QuadraticAlgebra Formalism.BasicNotions.Examples₂ Formalism.MainNotions.G
variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
namespace Formalism.L2.G
theorem _root_.solution : wU p n ^ 2 = (p : OO p n) := by
  unfold wU
  rw [GatR.om_sq, map_natCast]
end Formalism.L2.G
