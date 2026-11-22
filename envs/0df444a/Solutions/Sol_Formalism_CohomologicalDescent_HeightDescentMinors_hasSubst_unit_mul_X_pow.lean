-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_unit_mul_X_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:20:56.488845+00:00
-- url     : https://prove2.me/submissions/62e81996-8966-42f8-8237-1c0626299c85

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
variable {R : Type} [CommRing R]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) : HasSubst ((w : R⟦X⟧) * X ^ n) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  change PowerSeries.constantCoeff ((w : R⟦X⟧) * X ^ n) = 0
  simp [zero_pow hn.ne']
end Formalism.CohomologicalDescent.HeightDescentMinors
