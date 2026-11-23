-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.invSer_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:25.839104+00:00
-- url     : https://prove2.me/submissions/09f1fa5b-3836-4d49-bf08-4acc1e946f28

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_dI_cc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.ELL.CubeTwoAlt
open WeierstrassChordSeries
variable {K : Type u} [Field K]
local notation "cc" => MvPowerSeries.constantCoeff
variable {W : WeierstrassCurve K} {w : PowerSeries K}
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution (hw : WFixed W w) (i : Fin 2) :
    (invSer W w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X i * (dI W w i)⁻¹ := by
  have ha : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X i
  have hφc : PowerSeries.constantCoeff (-1 + C W.a₁ * X + C W.a₃ * w : PowerSeries K) ≠ 0 := by
    simp [hw.1]
  have e := congrArg (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K))
    (PowerSeries.mul_inv_cancel _ hφc)
  have hs : (-1 + C W.a₁ * X + C W.a₃ * w : PowerSeries K).subst
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = dI W w i := by
    rw [← PowerSeries.coe_substAlgHom ha]
    simp only [map_add, map_neg, map_one, map_mul]
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_C, PowerSeries.subst_C,
      PowerSeries.subst_X ha]
    rfl
  have h1 : (1 : PowerSeries K).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 1 := by
    rw [← PowerSeries.coe_substAlgHom ha, map_one]
  rw [PowerSeries.subst_mul ha, hs, h1] at e
  have hinv : (-1 + C W.a₁ * X + C W.a₃ * w : PowerSeries K)⁻¹.subst
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = (dI W w i)⁻¹ :=
    (MvPowerSeries.eq_inv_iff_mul_eq_one (by rw [dI_cc hw]; exact neg_ne_zero.mpr one_ne_zero)).mpr
      (by rw [mul_comm]; exact e)
  rw [invSer, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, hinv]
end Formalism.ELL.CubeTwoAlt
