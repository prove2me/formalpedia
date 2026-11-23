-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.subst_wU_X_mem_T_of_wFixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:14.268629+00:00
-- url     : https://prove2.me/submissions/cff7cab7-5a5b-4ce1-b966-5f6563be84dd

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_mem_T
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_w_coeff_mem


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
    (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ∈ T W := by
  classical
  rw [mem_T]; intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · rw [wU, PowerSeries.coeff_mk]; exact w_coeff_mem hw _
  · exact Subalgebra.zero_mem _
end Formalism.ELL.CubeTwoAlt
