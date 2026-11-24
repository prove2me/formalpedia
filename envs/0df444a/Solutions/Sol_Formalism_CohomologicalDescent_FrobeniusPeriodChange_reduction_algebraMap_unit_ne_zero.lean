-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.reduction_algebraMap_unit_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:41.639283+00:00
-- url     : https://prove2.me/submissions/d9faeb71-7b31-468b-b5e2-6716b7d9b96c

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
theorem _root_.solution (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] (red : O →+* F) (c : ℤ_[l])
    (hc : IsUnit c) : red (algebraMap ℤ_[l] O c) ≠ 0 := by
  exact ((hc.map (algebraMap ℤ_[l] O)).map red).ne_zero
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
