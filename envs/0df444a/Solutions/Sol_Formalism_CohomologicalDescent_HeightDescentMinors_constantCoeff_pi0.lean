-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.constantCoeff_pi0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:20.56899+00:00
-- url     : https://prove2.me/submissions/800c6a85-ddc3-4e3f-bc72-1bce1165e244

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_binomialSeriesSubOne
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_one_mem_mu

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
theorem _root_.solution : constantCoeff (pi0 l O) = 0 := by
  rw [pi0, map_prod]
  exact Finset.prod_eq_zero (one_mem_mu l) (constantCoeff_binomialSeriesSubOne l O 1)
end Formalism.CohomologicalDescent.HeightDescentMinors
