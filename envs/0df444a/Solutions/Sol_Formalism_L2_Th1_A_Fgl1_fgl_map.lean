-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.fgl_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:41.176619+00:00
-- url     : https://prove2.me/submissions/b78ba2ca-a6bd-4d1a-9015-9a2d585ad4f4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_mv_map_invOfUnit
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_dd_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_uThird_map
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wThird_map
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
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution : MvPowerSeries.map φ (fgl W) = fgl (W.map φ) := by
  simp only [fgl]
  rw [map_mul, mv_map_invOfUnit φ _ (-1) (-1) (by simpa using dd_cc W) (by simp)]
  simp [map_add, map_mul, uThird_map, wThird_map]
end Formalism.L2.Th1.A.Fgl1
