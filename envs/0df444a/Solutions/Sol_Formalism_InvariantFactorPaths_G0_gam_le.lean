-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G0.gam_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:06:34.106556+00:00
-- url     : https://prove2.me/submissions/4e5d8e12-7f4b-4ecb-8eb0-4d44e70e86d5

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ParamDefs
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G0
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.G0
theorem _root_.solution {p : ℝ} (hp : 5 ≤ p) : gam p ≤ 25 / (24 * p) := by
  unfold gam
  have h1 : 0 < p ^ 2 - 1 := by nlinarith
  have h2 : 0 < 24 * p := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith
end Formalism.InvariantFactorPaths.G0
