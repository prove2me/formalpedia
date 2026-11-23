-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.v_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:43.049557+00:00
-- url     : https://prove2.me/submissions/0db9b91e-02f3-4c87-a61f-33570b20f1ac

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_two_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_gx_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_gy_mem

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
open Formalism.ELL.VeluCoordinateMaps
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
variable {W : WeierstrassCurve K} (hW : IntegralModel W) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
include hW ha hb
namespace Formalism.ELL.VeluCoordinateMaps
theorem _root_.solution : veluV W a b ∈ unitBall K := by
  unfold veluV
  split_ifs
  · exact gx_mem hW ha hb
  · exact sub_mem (mul_mem two_mem (gx_mem hW ha hb)) (mul_mem (mem.mpr hW.1) (gy_mem hW ha hb))
end Formalism.ELL.VeluCoordinateMaps
