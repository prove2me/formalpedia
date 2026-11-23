-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.inverseSeries_subst_X1_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:06.070557+00:00
-- url     : https://prove2.me/submissions/aeaa6fab-f13e-4830-9d9d-ab9f94121b21

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
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_dI_mem_T_of_wFixed
import Theorems.Thm_Formalism_ELL_CubeTwoAlt_invSer_subst
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_X_mem_T
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_inv_mem_integralSeries


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
theorem _root_.solution (hw : WFixed W w) :
    (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∈ T W := by
  rw [invSer_subst hw]
  exact (T W).mul_mem (X_mem_T 1) (inv_mem_integralSeries (dI_mem_T_of_wFixed hw 1)
    (by rw [dI_cc hw]; exact neg_ne_zero.mpr one_ne_zero)
    (by rw [dI_cc hw, inv_neg, inv_one]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)))
end Formalism.ELL.CubeTwoAlt
