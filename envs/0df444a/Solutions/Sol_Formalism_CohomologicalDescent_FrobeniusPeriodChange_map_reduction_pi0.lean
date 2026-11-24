-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.map_reduction_pi0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:04:06.955825+00:00
-- url     : https://prove2.me/submissions/dcf59015-06c3-4432-a164-1ff505f493ed

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_map_reduction_binomialSeriesSubOne

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
variable (l : ℕ) [Fact l.Prime] (O k : Type) [CommRing O] [CommRing k] [Algebra ℤ_[l] O]
  [Algebra ℤ_[l] k] (red : O →+* k)
  (hred : ∀ z : ℤ_[l], red (algebraMap ℤ_[l] O z) = algebraMap ℤ_[l] k z)
include hred
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : PowerSeries.map red (pi0 l O) = pi0 l k := by
  unfold pi0
  rw [map_prod]
  exact Finset.prod_congr rfl fun d _ => map_reduction_binomialSeriesSubOne l O k red hred d
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
