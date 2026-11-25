-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.derivation_linear_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:16:47.809561+00:00
-- url     : https://prove2.me/submissions/4ed2754e-478a-4135-8298-ac6e82767188

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
theorem _root_.solution : DLinear := by
  intro A N _ _ _ p γA γ d htor hγadd hγsmul hd
  have hadd : ∀ x y, d (x + y) = d x + d y := by
    intro x y
    apply eq_of_sub_eq_zero
    apply htor
    rw [smul_sub, smul_add, hd, hd, hd, hγadd]
    abel
  refine ⟨hadd, ?_⟩
  intro a x ha
  apply eq_of_sub_eq_zero
  apply htor
  rw [smul_sub, hd, hγsmul, ha, smul_comm p a (d x), hd, smul_sub]
  exact sub_self _
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
