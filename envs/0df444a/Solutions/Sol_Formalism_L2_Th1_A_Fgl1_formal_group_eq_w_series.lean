-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.formal_group_eq_w_series
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:54.05637+00:00
-- url     : https://prove2.me/submissions/f7541824-8fa5-48b9-b575-8ac0d51ba8a8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_cThree_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_dd_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_dd_cc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Fgl1
local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff
variable {K : Type u} [Field K] (W : WeierstrassCurve K)
open Formalism.ELL.WeierstrassChordSeries (z3 w3 F2)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution : fgl W = F2 W (wSer W) := by
  have h3 : uThird W = z3 W (wSer W) := by
    unfold uThird z3
    rw [MvPowerSeries.invOfUnit_eq' _ _ (by rw [cThree_cc]; rfl)]
    rfl
  have h4 : wThird W = w3 W (wSer W) := by
    unfold wThird w3
    rw [h3]
    rfl
  unfold fgl F2
  rw [MvPowerSeries.invOfUnit_eq' _ _ (by rw [dd_cc]; simp), h3, h4]
  rfl
end Formalism.L2.Th1.A.Fgl1
