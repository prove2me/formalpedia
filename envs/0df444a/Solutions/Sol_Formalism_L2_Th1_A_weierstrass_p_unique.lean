-- Prove2me | solution 1 for Formalism.L2.Th1.A.weierstrass_p_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:12:38.463357+00:00
-- url     : https://prove2.me/submissions/a2e21196-27b2-4dd9-9dd9-8da0e5f38b7b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_of_ode
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_unique

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
open WpSh
namespace Formalism.L2.Th1.A
theorem _root_.solution : WpUnique.{u} := by
  intro K _ _ g2 g3 r r' h h'
  exact cleared_unique (cleared_of_ode h) (cleared_of_ode h')
end Formalism.L2.Th1.A
