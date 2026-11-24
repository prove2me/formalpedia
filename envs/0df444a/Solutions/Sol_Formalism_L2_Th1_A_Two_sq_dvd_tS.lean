-- Prove2me | solution 1 for Formalism.L2.Th1.A.Two.sq_dvd_tS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:31:27.451866+00:00
-- url     : https://prove2.me/submissions/b9070cc8-4d8f-449e-8254-8ad96c473611

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_Two_subst_tS
import Theorems.Thm_Formalism_ELL_EulerSeries_Agree_mul_right


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
theorem _root_.solution (xP : K) : X ^ 2 ∣ (tS W xP).subst (expSer W) := by
  rw [subst_tS]
  exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.mpr (e0 W)) 2) _
end Formalism.L2.Th1.A.Two
