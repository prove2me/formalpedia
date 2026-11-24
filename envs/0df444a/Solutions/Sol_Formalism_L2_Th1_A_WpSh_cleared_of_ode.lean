-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.cleared_of_ode
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:45:33.793293+00:00
-- url     : https://prove2.me/submissions/ed51649f-9579-4382-bd12-bda8b78dfc32

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_add_eq_mul
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_clearedM_of_ode
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_cleared_of_clearedM

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
open Formalism.L2.Th1.A.WpSh
variable {K : Type u} [Field K]
namespace Formalism.L2.Th1.A.WpSh
theorem _root_.solution {g2 g3 : K} {r : K⟦X⟧}
    (h : dL (uPow (-2) + toL r) ^ 2 = 4 * (uPow (-2) + toL r) ^ 3
      - HahnSeries.C g2 * (uPow (-2) + toL r) - HahnSeries.C g3) : Cleared g2 g3 r := by
  rw [add_eq_mul] at h
  exact cleared_of_clearedM (clearedM_of_ode h)
end Formalism.L2.Th1.A.WpSh
