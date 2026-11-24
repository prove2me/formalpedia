-- Prove2me | solution 1 for Formalism.L2.Th1.A.WpSh.cleared_of_clearedM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:20:13.653881+00:00
-- url     : https://prove2.me/submissions/0f56c422-d229-4f7c-862e-d746db7d39f6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_WpShape
import Theorems.Thm_Formalism_L2_Th1_A_WpSh_derivative_X_sq_mul

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
theorem _root_.solution {g2 g3 : K} {r : K⟦X⟧} (h : ClearedM g2 g3 (1 + X ^ 2 * r)) :
    Cleared g2 g3 r := by
  unfold ClearedM at h
  unfold Cleared
  rw [map_add, Derivation.map_one_eq_zero, derivative_X_sq_mul] at h
  have e : X * (0 + (2 * X * r + X ^ 2 * derivative K r)) - 2 * (1 + X ^ 2 * r)
      = -2 + X ^ 3 * derivative K r := by ring
  rw [e] at h
  exact h
end Formalism.L2.Th1.A.WpSh
