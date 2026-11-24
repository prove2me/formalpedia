-- Prove2me | solution 1 for Formalism.L2.Th1.A.wpShape_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:32:53.357148+00:00
-- url     : https://prove2.me/submissions/953285db-2ac3-48d4-8171-986931e5cce0

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_low
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_odd
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_wpL_shape

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
theorem _root_.solution (hE : ExpSpec.{u}) (hO : WpODE.{u}) : WpShape.{u} := by
  intro K _ _ W
  obtain ⟨h1, h2⟩ := wpL_shape hE hO W
  obtain ⟨a, _, c, d⟩ := cleared_low h2
  exact ⟨h1, a, fun n hn => cleared_odd h2 n hn, c, d⟩
end Formalism.L2.Th1.A
