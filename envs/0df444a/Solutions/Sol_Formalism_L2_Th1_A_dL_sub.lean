-- Prove2me | solution 1 for Formalism.L2.Th1.A.dL_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:13:09.829384+00:00
-- url     : https://prove2.me/submissions/c4ac5708-94cc-44be-83ac-407a9687297f

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {R : Type u} [CommRing R]
namespace Formalism.L2.Th1.A
theorem _root_.solution (f g : LaurentSeries R) : dL (f - g) = dL f - dL g := by
  exact map_sub dL f g
end Formalism.L2.Th1.A
