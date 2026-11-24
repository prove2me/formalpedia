-- Prove2me | solution 1 for Formalism.L2.Th1.A.Two.subst_tS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:44:17.888062+00:00
-- url     : https://prove2.me/submissions/ea7247b6-8f77-448a-966d-a15e37266363

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow


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
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.Two
theorem _root_.solution (xP : K) : (tS W xP).subst (expSer W)
    = expSer W ^ 2 * (invOfUnit (tDen W xP) 1).subst (expSer W) := by
  rw [tS, ← PowerSeries.coe_substAlgHom (he W), map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X (he W)]
end Formalism.L2.Th1.A.Two
