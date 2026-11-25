-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.semilinear_change_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:27:15.708322+00:00
-- url     : https://prove2.me/submissions/874eaa43-ccf8-474e-85e4-fe9e9de97b35

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
theorem _root_.solution : SemilinChange := by
  intro R _ n θ M g g' y
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul,
    ← Matrix.mulVec_mulVec]
  congr 1
  funext a
  rw [RingHom.map_mulVec]
  rfl
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
