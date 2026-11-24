-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.hasSubst_gammaSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:07.583342+00:00
-- url     : https://prove2.me/submissions/c895a3f0-17c0-47f2-b35e-1ede238b7f04

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_constantCoeff_gammaSeries

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
theorem _root_.solution (lam : R) (un : R⟦X⟧) : HasSubst (gamSer lam un) := by
  first
  | exact HasSubst.of_constantCoeff_zero (constantCoeff_gammaSeries lam un)
  | exact PowerSeries.HasSubst.of_constantCoeff_zero (constantCoeff_gammaSeries lam un)
  | exact HasSubst.of_constantCoeff_zero' (constantCoeff_gammaSeries lam un)
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
