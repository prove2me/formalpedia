-- Prove2me | solution 1 for Formalism.L2.Th1.A.Two.toL_exp_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:31:16.115915+00:00
-- url     : https://prove2.me/submissions/39a8d3e0-0424-4606-82f2-21d8fb6c1c4d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_expSpec


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
theorem _root_.solution : toL (expSer W) ≠ 0 := by
  intro h
  have h1 := (expSpec K W).2.1
  rw [(map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h, map_zero] at h1
  exact zero_ne_one h1
end Formalism.L2.Th1.A.Two
