-- Prove2me | solution 1 for Formalism.ELL.DeuringModel.norm_add_eq_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:10:02.946364+00:00
-- url     : https://prove2.me/submissions/c34bc84a-710f-4b7f-8633-f57b994cece4

import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LegendreInvariant
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_Deuring

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.ELL
open Formalism.ELL.DeuringModel
open Polynomial
variable {K : Type*} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.DeuringModel
theorem _root_.solution {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]
end Formalism.ELL.DeuringModel
