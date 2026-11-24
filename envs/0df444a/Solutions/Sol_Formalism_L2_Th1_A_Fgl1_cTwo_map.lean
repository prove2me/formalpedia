-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.cTwo_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:26:43.319924+00:00
-- url     : https://prove2.me/submissions/fcbdc3ae-99be-4a95-96b3-f4dab8b0a21c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_lam_map
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_nu_map

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
theorem _root_.solution : MvPowerSeries.map φ (cTwo W) = cTwo (W.map φ) := by
  simp [cTwo, map_add, map_mul, map_pow, lam_map, nu_map, map_ofNat]
end Formalism.L2.Th1.A.Fgl1
