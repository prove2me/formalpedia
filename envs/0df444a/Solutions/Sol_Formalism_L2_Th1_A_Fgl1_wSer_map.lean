-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.wSer_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:33.421807+00:00
-- url     : https://prove2.me/submissions/17a32a3d-888c-4fc9-9a91-1260281e1ad6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_unique

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
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution (φ : R →+* S) : PowerSeries.map φ (wSer W) = wSer (W.map φ) := by
  refine wSer_unique (W.map φ) ⟨?_, ?_⟩
  · have h0 := (wSer_fixed W).1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · have h := congrArg (PowerSeries.map φ) (wSer_fixed W).2
    simpa [map_add, map_mul, map_pow] using h
end Formalism.L2.Th1.A.Fgl1
