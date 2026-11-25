-- Prove2me | solution 1 for Formalism.L2.Th1.A.ZSer.ring_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:42:48.992693+00:00
-- url     : https://prove2.me/submissions/f1940739-2ab0-463f-a37b-2d4aaf373e93

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementG
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CompInv
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_LogExp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FormalGroupEqWSeries
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_SubstPairSubst
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_FF_map
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_zSer_cc
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_zSer_map
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_field_add
import Theorems.Thm_Formalism_L2_Th1_A_ZSer_zSer_univ
import Theorems.Thm_Formalism_L2_Th1_A_Univ_map_eq
import Theorems.Thm_Formalism_L2_Th1_A_Univ_ps_transfer


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
open Formalism.L2.Th1.A.ZSer
local notation "FF[" W "](" a ", " b ")" =>
  MvPowerSeries.subst (![a, b] : Fin 2 → PowerSeries _) (fgl W)
open Univ
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.ZSer
theorem _root_.solution (hL : FglLog.{0}) (m n : ℤ) :
    FF[W](zSer W m, zSer W n) = zSer W (m + n) := by
  have h : PowerSeries.map Univ.ι (FF[W₀](zSer W₀ m, zSer W₀ n))
      = PowerSeries.map Univ.ι (zSer W₀ (m + n)) := by
    rw [FF_map W₀ Univ.ι (zSer_cc W₀ m) (zSer_cc W₀ n), zSer_map, zSer_map, zSer_map]
    exact field_add Univ.WK hL m n
  have h2 := Univ.ps_transfer W h
  rw [FF_map W₀ (Univ.φ_of W) (zSer_cc W₀ m) (zSer_cc W₀ n), zSer_univ, zSer_univ, zSer_univ,
    Univ.map_eq] at h2
  exact h2
end Formalism.L2.Th1.A.ZSer
