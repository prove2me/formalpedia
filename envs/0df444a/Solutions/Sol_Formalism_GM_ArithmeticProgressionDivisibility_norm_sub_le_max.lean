-- Prove2me | solution 1 for Formalism.GM.ArithmeticProgressionDivisibility.norm_sub_le_max
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:55.967384+00:00
-- url     : https://prove2.me/submissions/9a0b11d4-71fa-46f7-b08b-7ff832f37340

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
omit [NormedAlgebra ℚ_[p] K]
namespace Formalism.GM.ArithmeticProgressionDivisibility
theorem _root_.solution [IsUltrametricDist K] (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  have h := IsUltrametricDist.norm_add_le_max x (-y)
  rwa [← sub_eq_add_neg, norm_neg] at h
end Formalism.GM.ArithmeticProgressionDivisibility
