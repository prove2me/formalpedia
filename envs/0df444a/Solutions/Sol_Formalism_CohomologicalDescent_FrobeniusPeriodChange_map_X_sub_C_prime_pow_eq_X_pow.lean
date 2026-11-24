-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.map_X_sub_C_prime_pow_eq_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:55:14.267751+00:00
-- url     : https://prove2.me/submissions/8df713d3-eefe-416a-bdb8-b6d1179da650

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution (l : ℕ) [CharP F l] (red : O →+* F) (m : ℕ) :
    PowerSeries.map red ((X - C (l : O)) ^ m) = X ^ m := by
  rw [map_pow, map_sub, map_X, map_C, map_natCast, CharP.cast_eq_zero, map_zero, sub_zero]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
