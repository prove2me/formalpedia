-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.wThird_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:43:10.514573+00:00
-- url     : https://prove2.me/submissions/d56ab203-b4c4-4cb6-8b75-cfdd7a103c62

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_lam_map
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_nu_map
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_uThird_map

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
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution : MvPowerSeries.map φ (wThird W) = wThird (W.map φ) := by
  simp [wThird, map_add, map_mul, lam_map, uThird_map, nu_map]
end Formalism.L2.Th1.A.Fgl1
