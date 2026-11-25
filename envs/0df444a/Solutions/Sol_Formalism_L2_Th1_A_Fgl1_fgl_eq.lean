-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.fgl_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:09:51.176264+00:00
-- url     : https://prove2.me/submissions/73e09f3c-2639-4baf-99da-c4600163afdb

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_uThird_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_dd_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wThird_eq
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
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution : fgl W = (iSer W).subst (uThird W) := by
  have ha : PowerSeries.HasSubst (uThird W) := HasSubst.of_constantCoeff_zero (uThird_cc W)
  have hic : constantCoeff (iDen W) = ((-1 : Rˣ) : R) := by
    simp [iDen, (wSer_fixed W).1]
  have e := congrArg (PowerSeries.subst (uThird W)) (PowerSeries.mul_invOfUnit (iDen W) (-1) hic)
  have hs : (iDen W).subst (uThird W) = dd W := by
    unfold iDen
    rw [← PowerSeries.coe_substAlgHom ha]
    simp only [map_add, map_neg, map_one, map_mul]
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_C, PowerSeries.subst_C,
      PowerSeries.subst_X ha, ← wThird_eq]
  have h1 : (1 : PowerSeries R).subst (uThird W) = 1 := by
    rw [← PowerSeries.coe_substAlgHom ha, map_one]
  rw [PowerSeries.subst_mul ha, hs, h1] at e
  have e2 : dd W * MvPowerSeries.invOfUnit (dd W) (-1) = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by rw [dd_cc]; simp)
  have hinv : (invOfUnit (iDen W) (-1)).subst (uThird W) = MvPowerSeries.invOfUnit (dd W) (-1) :=
    left_inv_eq_right_inv (by rw [mul_comm]; exact e) e2
  rw [iSer, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, hinv, fgl]
end Formalism.L2.Th1.A.Fgl1
