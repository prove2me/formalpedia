-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.three_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:21.981726+00:00
-- url     : https://prove2.me/submissions/dd22cac6-2fd1-4d78-afdd-67227bf4bda3

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_mem
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_norm_three_le


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
namespace Formalism.ELL.VeluCoordinateMaps
theorem _root_.solution : (3 : K) ∈ unitBall K := mem.mpr FormalGroupPointsParam.norm_three_le
end Formalism.ELL.VeluCoordinateMaps
