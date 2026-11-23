-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:56.117559+00:00
-- url     : https://prove2.me/submissions/8931e531-da9d-413f-9068-9c0782ea9cae

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion
import Theorems.Thm_Formalism_ELL_FormalGroupPointsTorsion_add_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsTorsion
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.FormalGroupPointsTorsion
theorem _root_.solution {a b : K} {c : ℝ} (ha : ‖a‖ < c) (hb : ‖b‖ < c) : ‖a - b‖ < c := by
  rw [sub_eq_add_neg]; exact add_lt ha (by rwa [norm_neg])
end Formalism.ELL.FormalGroupPointsTorsion
