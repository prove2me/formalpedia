-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.gx_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:26:52.456109+00:00
-- url     : https://prove2.me/submissions/26844213-538e-45dc-948f-fdfb46dbb7a7

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_two_mem
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_three_mem

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
theorem _root_.solution : veluGx W a b ∈ unitBall K := by
  unfold veluGx
  exact sub_mem (add_mem (add_mem (mul_mem three_mem (pow_mem (mem.mpr ha) 2))
    (mul_mem (mul_mem two_mem (mem.mpr hW.2.1)) (mem.mpr ha))) (mem.mpr hW.2.2.2.1))
    (mul_mem (mem.mpr hW.1) (mem.mpr hb))
end Formalism.ELL.VeluCoordinateMaps
