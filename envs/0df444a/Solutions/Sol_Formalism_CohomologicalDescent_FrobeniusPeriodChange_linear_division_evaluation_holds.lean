-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.linear_division_evaluation_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:24:33.070889+00:00
-- url     : https://prove2.me/submissions/c223b79f-e285-4f15-8c36-728b76a8077b

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
theorem _root_.solution : LinDivisionEval := by
  intro O _ _ _ _ _ _ _ c a f f₁ hn hf
  have hx : PowerSeries.HasEval c := hn
  have hc : Continuous (RingHom.id O) := continuous_id
  have h2 := congrArg (PowerSeries.eval₂Hom hc hx) hf
  rw [map_add, map_mul, map_sub] at h2
  simp only [PowerSeries.coe_eval₂Hom, eval₂_C, eval₂_X, RingHom.id_apply, sub_self,
    zero_mul, zero_add] at h2
  exact h2
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
