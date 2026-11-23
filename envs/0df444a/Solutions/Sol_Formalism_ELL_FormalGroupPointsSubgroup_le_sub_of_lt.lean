-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsSubgroup.le_sub_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:01.393783+00:00
-- url     : https://prove2.me/submissions/999bc93d-99c8-49cf-8461-7d8ee6a41fa7

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds

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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupPointsSubgroup
open WeierstrassCurve Polynomial
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.FormalGroupPointsSubgroup
theorem _root_.solution {a b : K} (h : ‖b‖ < ‖a‖) : ‖a‖ ≤ ‖a - b‖ := by
  have h1 : ‖a‖ ≤ max ‖a - b‖ ‖b‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (a - b) b
  rcases le_max_iff.mp h1 with h2 | h2
  · exact h2
  · exact absurd h2 (not_le.mpr h)
end Formalism.ELL.FormalGroupPointsSubgroup
