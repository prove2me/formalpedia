-- Prove2me | solution 1 for Formalism.ELL.VeluIntegrality.mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:43.619832+00:00
-- url     : https://prove2.me/submissions/e0c60f59-3962-483a-9909-950b573613ca

import Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_VeluInt

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
open Formalism.ELL.VeluIntegrality
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.VeluIntegrality
theorem _root_.solution {x : K} : x ∈ (ball : Subring K) ↔ ‖x‖ ≤ 1 := Iff.rfl
end Formalism.ELL.VeluIntegrality
