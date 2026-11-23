-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.gy_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:13:02.166723+00:00
-- url     : https://prove2.me/submissions/e37aedf0-9c43-441b-8ebf-35782f826d64

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries

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
theorem _root_.solution : veluGy (W.map f) (f a) (f b) = f (veluGy W a b) := by
  simp [veluGy, map_sub, map_mul, map_neg, map_ofNat]
end Formalism.ELL.VeluCoordinateMaps
