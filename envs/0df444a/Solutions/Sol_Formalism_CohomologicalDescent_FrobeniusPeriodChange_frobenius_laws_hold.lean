-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.frobenius_laws_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:04:53.538392+00:00
-- url     : https://prove2.me/submissions/eccc778e-57b6-4aec-b7a9-048ce148fb28

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_subst_C_eq_C

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
theorem _root_.solution : FrobLaws := by
  intro R _ l hl
  have hc : constantCoeff (X ^ l : R⟦X⟧) = 0 := by
    rw [map_pow, constantCoeff_X, zero_pow hl.ne']
  have hs : HasSubst (X ^ l : R⟦X⟧) := by
    first
    | exact HasSubst.of_constantCoeff_zero hc
    | exact PowerSeries.HasSubst.of_constantCoeff_zero hc
    | exact HasSubst.of_constantCoeff_zero' hc
  refine ⟨fun f g => ?_, fun f g => ?_, fun a => ?_, ?_⟩
  · exact subst_add hs f g
  · exact subst_mul hs f g
  · exact subst_C_eq_C a
  · exact subst_X hs
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
