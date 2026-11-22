-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_br_padic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:04.609804+00:00
-- url     : https://prove2.me/submissions/12936e70-a9b2-4a67-9710-a2a33706d048

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_binomialSeriesSubOne

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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (c : ℤ_[l]) : HasSubst (br l O c) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  change PowerSeries.constantCoeff (br l O c) = 0
  exact constantCoeff_binomialSeriesSubOne l O c
end Formalism.CohomologicalDescent.HeightDescentMinors
