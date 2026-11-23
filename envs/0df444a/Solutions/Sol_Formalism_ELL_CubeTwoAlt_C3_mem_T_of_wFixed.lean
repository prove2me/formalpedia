-- Prove2me | solution 1 for Formalism.ELL.CubeTwoAlt.C3_mem_T_of_wFixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:31.05122+00:00
-- url     : https://prove2.me/submissions/e17689ff-3b55-40bd-927d-a9ed5b50ba05

import Definitions.Def_Formalism_EllipticTorsion_CoeffRing
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WChord
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ExistsUnitFactor
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsHomDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_CubeTwo
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_constSeries_mem_integralSeries
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_lineCoeffCubic_mem
import Theorems.Thm_Formalism_ELL_WeierstrassChordSeries_slope_mem_integralSeries


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
variable {K : Type u} [Field K] {W : WeierstrassCurve K} {w : PowerSeries K}
local notation "cc" => MvPowerSeries.constantCoeff
namespace Formalism.ELL.CubeTwoAlt
theorem _root_.solution (hw : WFixed W w) : C3 W w ∈ T W :=
  lineCoeffCubic_mem _ (constSeries_mem_integralSeries (by simp)) (constSeries_mem_integralSeries (by simp)) (constSeries_mem_integralSeries (by simp)) (slope_mem_integralSeries hw)
end Formalism.ELL.CubeTwoAlt
