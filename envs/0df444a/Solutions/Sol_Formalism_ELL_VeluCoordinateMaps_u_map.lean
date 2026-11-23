-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.u_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:22.385167+00:00
-- url     : https://prove2.me/submissions/ce63cb2e-cab2-489c-8471-318e9669f177

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_gy_map

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
variable {K L : Type*} [Field K] [Field L] (f : K →+* L) (W : WeierstrassCurve K) (a b : K)
namespace Formalism.ELL.VeluCoordinateMaps
theorem _root_.solution : veluU (W.map f) (f a) (f b) = f (veluU W a b) := by
  simp [veluU, gy_map]
end Formalism.ELL.VeluCoordinateMaps
