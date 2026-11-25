-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.det_dvd_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:16:49.295073+00:00
-- url     : https://prove2.me/submissions/8fe1370d-e755-4bf4-98fc-3394e96ce8e3

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
theorem _root_.solution : DetDvd := by
  intro R _ n h x P Q hPQ
  refine ⟨Q.det, ?_⟩
  have h2 := congrArg Matrix.det hPQ
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h2
  rw [h2, ← pow_mul]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
