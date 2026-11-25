-- Prove2me | solution 1 for Formalism.L2.Th1.A.Fgl1.wThird_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:00:59.134242+00:00
-- url     : https://prove2.me/submissions/b109dc41-972a-4609-9f5a-ef9186323104

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_sub_cancel
import Theorems.Thm_P2M_Formalism_L2_Th1_A_Fgl1_vieta__8a16bc0c9e24
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_weq_iff
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_lam_mul
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_cThree_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_uThird_cc
import Theorems.Thm_Formalism_L2_Th1_A_Fgl1_wThird_cc
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lam_mul
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_weq_iff
import Theorems.Thm_Formalism_ELL_wSubstUnique


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
open Formalism.ELL.WeierstrassChordSeries (G c3 c2)
namespace Formalism.L2.Th1.A.Fgl1
theorem _root_.solution : wThird W = (wSer W).subst (uThird W) := by
  have hw := wSer_fixed W
  have hUs := fun (s : MvPowerSeries (Fin 2) R) (hs : cc s = 0) =>
    Formalism.ELL.wSubstUnique R W (wSer W) hw (Fin 2) s hs
  have h0 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 0) (by simp)).1
  have h1 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 1) (by simp)).1
  have hW0 : Wi W 0 = lam W * MvPowerSeries.X 0 + nu W := by unfold nu; ring
  have hW1 : Wi W 1 = lam W * MvPowerSeries.X 1 + nu W := by
    have := lam_mul W; unfold nu; linear_combination -this
  change G _ _ _ _ _ _ (Wi W 0) = 0 at h0
  change G _ _ _ _ _ _ (Wi W 1) = 0 at h1
  have hinv : cThree W * MvPowerSeries.invOfUnit (cThree W) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by rw [cThree_cc]; rfl)
  have he1 : c3 (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) (lam W) *
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + uThird W) +
      c2 (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
        (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) (lam W) (nu W) = 0 := by
    change cThree W * _ + cTwo W = 0
    rw [uThird]
    linear_combination (-cTwo W) * hinv
  rw [hW0] at h0
  rw [hW1] at h1
  have hG3 := vieta' (fun f hf => sub_cancel hf) h0 h1 he1
  exact (hUs (uThird W) (uThird_cc W)).2 (wThird W) (wThird_cc W) ((weq_iff W _ _).mpr hG3)
end Formalism.L2.Th1.A.Fgl1
