-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.uThird_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:34:08.883932+00:00
-- url     : https://prove2.me/submissions/b7744910-b42f-4882-8192-00212154de1b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_mv_map_invOfUnit
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_cThree_map
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_cTwo_map
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_cThree_cc

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
theorem _root_.solution : MvPowerSeries.map φ (uThird W) = uThird (W.map φ) := by
  simp only [uThird, map_sub, map_neg, map_mul, MvPowerSeries.map_X, cTwo_map]
  rw [mv_map_invOfUnit φ (cThree W) 1 1 (by simp [cThree_cc]) (by simp), cThree_map]
end Formalism.L2.Th1.A.Fgl1
