-- Prove2me | solution 1 for Formalism.GM.ArithmeticProgressionDivisibility.norm_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:54.723795+00:00
-- url     : https://prove2.me/submissions/9aff0217-7e82-4d79-9777-783bb5792614

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset
open Formalism.GM.ArithmeticProgressionDivisibility
variable {p : ℕ} [hp : Fact p.Prime] {K : Type} [NormedField K] [NormedAlgebra ℚ_[p] K]
namespace Formalism.GM.ArithmeticProgressionDivisibility
theorem _root_.solution (k : ℤ) : ‖(k : K)‖ = ‖(k : ℚ_[p])‖ := by
  rw [← map_intCast (algebraMap ℚ_[p] K) k, norm_algebraMap']
end Formalism.GM.ArithmeticProgressionDivisibility
