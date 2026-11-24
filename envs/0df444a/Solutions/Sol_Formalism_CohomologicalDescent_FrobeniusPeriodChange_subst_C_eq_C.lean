-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.subst_C_eq_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:56:33.214837+00:00
-- url     : https://prove2.me/submissions/419e6e61-eedd-4dee-832c-f78c1cacb8d4

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
variable {R : Type} [CommRing R]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution {a : R⟦X⟧} (r : R) : (C r : R⟦X⟧).subst a = C r := by
  rw [subst_C]; rfl
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
