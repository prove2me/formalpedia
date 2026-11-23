-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.cleared_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:40.104071+00:00
-- url     : https://prove2.me/submissions/8da06345-b3a4-400b-b9c9-06d79ce8b6e6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape

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
theorem _root_.solution {g2 g3 : K} {r : K⟦X⟧} (h : Cleared g2 g3 r) :
    4 * (X * derivative K r) + 12 * r =
      X ^ 2 * (C g2 + C g3 * X ^ 2 + C g2 * X ^ 2 * r - 12 * r ^ 2 - 4 * X ^ 2 * r ^ 3
        + X ^ 2 * derivative K r ^ 2) := by
  unfold Cleared at h
  have hX : (X : K⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
  apply mul_left_cancel₀ hX
  linear_combination (-1 : K⟦X⟧) * h
end Formalism.L2.Th1.A.WpSh
