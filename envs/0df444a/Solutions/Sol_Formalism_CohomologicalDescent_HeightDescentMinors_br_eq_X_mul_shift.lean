-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.br_eq_X_mul_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:04.379201+00:00
-- url     : https://prove2.me/submissions/953c4c7c-c62c-427a-bc69-0feab9bab42e

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
variable (l : ℕ) [Fact l.Prime]
variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (d : ℤ_[l]) :
    br l O d = X * PowerSeries.mk (fun n => coeff (n + 1) (br l O d)) := by
  ext n
  rcases n with _ | n
  · simpa using constantCoeff_binomialSeriesSubOne l O d
  · simp [PowerSeries.coeff_succ_X_mul]
end Formalism.CohomologicalDescent.HeightDescentMinors
