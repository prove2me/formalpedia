-- Prove2me | solution 1 for Formalism.ThetaLiftIndependence.DeterminantSwapLemmas.equiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:37.820287+00:00
-- url     : https://prove2.me/submissions/25b7677a-296e-4022-90c8-798d59778d36

import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_ThetaLiftIndependence_ThetaOrbitSums_DetSwap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ThetaLiftIndependence
open Formalism.ThetaLiftIndependence.DeterminantSwapLemmas
variable {𝕜 E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
namespace Formalism.ThetaLiftIndependence.DeterminantSwapLemmas
theorem _root_.solution (T : E →ₗ[𝕜] F) (x : (LinearMap.ker T)ᗮ) :
    ((equiv T x : (LinearMap.ker (LinearMap.adjoint T))ᗮ) : F) = T x := rfl
end Formalism.ThetaLiftIndependence.DeterminantSwapLemmas
