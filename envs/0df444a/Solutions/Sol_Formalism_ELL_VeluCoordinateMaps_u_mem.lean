-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.u_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:13.293304+00:00
-- url     : https://prove2.me/submissions/20134c70-85d7-41de-ad0c-3d21b227756e

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
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
theorem _root_.solution : veluU W a b ∈ unitBall K := pow_mem (gy_mem hW ha hb) 2
end Formalism.ELL.VeluCoordinateMaps
