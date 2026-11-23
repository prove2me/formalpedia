-- Prove2me | solution 1 for Formalism.GM.ArithmeticProgressionDivisibility.progr_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:56.183821+00:00
-- url     : https://prove2.me/submissions/25992963-f5fc-47a7-85d6-350c213794f3

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
theorem _root_.solution (t₀ d : ℤ) (a b : ℕ) : progr t₀ d a - progr t₀ d b = d * ((a : ℤ) - b) := by
  unfold progr
  ring
end Formalism.GM.ArithmeticProgressionDivisibility
