-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.unit_pow_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:20:23.378106+00:00
-- url     : https://prove2.me/submissions/ac5f4081-5395-4369-9af4-b9471384eda7

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
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : UnitPow := by
  intro k _ h x x' hxx
  obtain ⟨α, hα, hassoc⟩ := (dvd_prime_pow X_prime h).1 ⟨x', hxx.symm⟩
  obtain ⟨u, hu⟩ := hassoc.symm
  exact ⟨α, u, hα, by rw [← hu, mul_comm]⟩
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
