-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.dI_mem_T_of_wFixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:47.259985+00:00
-- url     : https://prove2.me/submissions/b920383e-99ea-4589-a5a6-52c1150d9919

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_X_mem_T
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constSeries_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_wVar_mem_integralSeries


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
theorem _root_.solution (hw : WFixed W w) (i : Fin 2) : dI W w i ∈ T W :=
  (T W).add_mem ((T W).add_mem ((T W).neg_mem (T W).one_mem)
    ((T W).mul_mem (constSeries_mem_integralSeries (by simp)) (X_mem_T i))) ((T W).mul_mem (constSeries_mem_integralSeries (by simp)) (wVar_mem_integralSeries hw i))
end Formalism.ELL.CubeTwoAlt
