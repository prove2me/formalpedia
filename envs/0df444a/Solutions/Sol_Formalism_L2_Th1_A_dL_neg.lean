-- Prove2me | solution 1 for Formalism.L2.Th1.A.dL_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:56.739153+00:00
-- url     : https://prove2.me/submissions/526686f4-64f1-4461-9bab-2176b960aba1

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
theorem _root_.solution (f : LaurentSeries R) : dL (-f) = - dL f := by
  exact map_neg dL f
end Formalism.L2.Th1.A
