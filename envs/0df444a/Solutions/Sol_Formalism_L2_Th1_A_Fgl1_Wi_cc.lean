-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.Wi_cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:19:36.150875+00:00
-- url     : https://prove2.me/submissions/5a5103e5-1b42-4dc6-9c05-225a27575f44

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_coeff_Wi
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_coeff_Wi


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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution (i : Fin 2) : cc (Wi W i) = 0 := by
  have h0 : coeff 0 (wSer W) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (wSer_fixed W).1
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Wi]
  simp [h0]
end Formalism.L2.Th1.A.Fgl1
