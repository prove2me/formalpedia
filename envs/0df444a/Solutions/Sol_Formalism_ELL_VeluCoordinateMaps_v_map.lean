-- Prove2me | solution 1 for Formalism.ELL.VeluCoordinateMaps.v_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:22.642536+00:00
-- url     : https://prove2.me/submissions/a575851d-89b0-47c3-a784-b3c22a4a39a6

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WPoint
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsParamDef
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluUSeries
import Theorems.Thm_Formalism_ELL_VeluCoordinateMaps_gx_map
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
theorem _root_.solution : veluV (W.map f) (f a) (f b) = f (veluV W a b) := by
  unfold veluV
  rw [gx_map, gy_map]
  by_cases h : veluGy W a b = 0
  · rw [if_pos (by rw [h, map_zero]), if_pos h]
  · rw [if_neg (by rwa [map_eq_zero_iff f f.injective]), if_neg h]
    simp [map_sub, map_mul, map_ofNat]
end Formalism.ELL.VeluCoordinateMaps
