-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsSubgroup.sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:53.732451+00:00
-- url     : https://prove2.me/submissions/ee442ec4-e162-4ff6-9098-547a60ffbbf6

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsSubgroupHolds
import Theorems.Thm_Formalism_ELL_FormalGroupPointsSubgroup_add_le

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
theorem _root_.solution {a b : K} {c : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ c) : ‖a - b‖ ≤ c := by
  rw [sub_eq_add_neg]
  exact add_le ha (by rwa [norm_neg])
end Formalism.ELL.FormalGroupPointsSubgroup
