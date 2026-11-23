-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsSubgroup.mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:01.880879+00:00
-- url     : https://prove2.me/submissions/2e9b603d-263f-4b16-a701-e62253d8ac73

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
theorem _root_.solution {a b : K} {c d : ℝ} (ha : ‖a‖ ≤ c) (hb : ‖b‖ ≤ d) : ‖a * b‖ ≤ c * d := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) ((norm_nonneg _).trans ha)
end Formalism.ELL.FormalGroupPointsSubgroup
