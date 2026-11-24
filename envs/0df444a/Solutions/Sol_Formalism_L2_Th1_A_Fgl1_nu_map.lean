-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.nu_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:00:11.144111+00:00
-- url     : https://prove2.me/submissions/7dd91fd2-b8f8-4db7-bdc3-911337afd348

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_map
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_lam_map

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
theorem _root_.solution : MvPowerSeries.map φ (nu W) = nu (W.map φ) := by
  simp only [nu, map_sub, map_mul, MvPowerSeries.map_X, lam_map]
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.X 0), MvPowerSeries.map_X, wSer_map]
end Formalism.L2.Th1.A.Fgl1
