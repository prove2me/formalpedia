-- Prove2me | solution 1 for Formalism.ELL.FormalGroupPointsTorsion.mul_le_of_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:59.274744+00:00
-- url     : https://prove2.me/submissions/05897bb6-f9c8-42b1-a1d0-77f52aa22977

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsTorsionFree
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_FormalGroupPointsNoPrimeToPTorsion

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
theorem _root_.solution {a b : K} (ha : ‖a‖ ≤ 1) : ‖a * b‖ ≤ ‖b‖ := by
  rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) ha
end Formalism.ELL.FormalGroupPointsTorsion
