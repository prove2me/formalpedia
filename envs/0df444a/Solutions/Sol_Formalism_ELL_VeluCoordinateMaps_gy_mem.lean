-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.gy_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:41.885923+00:00
-- url     : https://prove2.me/submissions/d4ef95c4-9621-42ae-8402-43ba06885ac8

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_two_mem

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
theorem _root_.solution : veluGy W a b ∈ unitBall K := by
  unfold veluGy
  exact sub_mem (sub_mem (mul_mem (neg_mem two_mem) (mem.mpr hb)) (mul_mem (mem.mpr hW.1) (mem.mpr ha)))
    (mem.mpr hW.2.2.1)
end Formalism.ELL.VeluCoordinateMaps
