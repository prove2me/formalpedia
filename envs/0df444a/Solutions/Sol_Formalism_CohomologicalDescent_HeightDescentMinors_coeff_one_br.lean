-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.coeff_one_br
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:56.305799+00:00
-- url     : https://prove2.me/submissions/1147d31e-e89d-4f0e-a5c4-60ee886edad9

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

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
theorem _root_.solution (d : ℤ_[l]) : coeff 1 (br l O d) = algebraMap ℤ_[l] O d := by
  first
    | simp [br, PowerSeries.binomialSeries_coeff, Ring.choose_one_right, Algebra.smul_def]
    | simp [br, PowerSeries.binomialSeries, Ring.choose_one_right, Algebra.smul_def]
    | simp [br, PowerSeries.binomialSeries, Ring.choose_one_right]
end Formalism.CohomologicalDescent.HeightDescentMinors
