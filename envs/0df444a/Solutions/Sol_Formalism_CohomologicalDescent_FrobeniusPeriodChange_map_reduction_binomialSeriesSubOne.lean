-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.map_reduction_binomialSeriesSubOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:40.111106+00:00
-- url     : https://prove2.me/submissions/2c14377f-c29a-4085-aedb-0e7d56558a89

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_binomialSeriesSubOne_algebraMap


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
theorem _root_.solution (c : ℤ_[l]) : PowerSeries.map red (br l O c) = br l k c := by
  rw [← map_binomialSeriesSubOne_algebraMap l O c, ← map_binomialSeriesSubOne_algebraMap l k c]
  ext n
  simp [hred]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
