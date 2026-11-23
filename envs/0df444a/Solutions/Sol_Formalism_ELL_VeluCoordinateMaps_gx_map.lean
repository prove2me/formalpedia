-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.gx_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:06.619803+00:00
-- url     : https://prove2.me/submissions/b586ca66-4c95-4cd2-899b-2d4fa294db10

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
theorem _root_.solution : veluGx (W.map f) (f a) (f b) = f (veluGx W a b) := by
  simp [veluGx, map_sub, map_add, map_mul, map_ofNat]
end Formalism.ELL.VeluCoordinateMaps
