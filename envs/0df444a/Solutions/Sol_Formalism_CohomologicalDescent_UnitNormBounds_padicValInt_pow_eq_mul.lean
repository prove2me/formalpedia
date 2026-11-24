-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.padicValInt_pow_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:02:39.231675+00:00
-- url     : https://prove2.me/submissions/1028ffd3-0210-4c8b-b830-f820fe3302e4

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.UnitNormBounds
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
namespace Formalism.CohomologicalDescent.UnitNormBounds
theorem _root_.solution (l : ℕ) [Fact l.Prime] (x : ℤ) (_hx : x ≠ 0) (m : ℕ) :
    padicValInt l (x ^ m) = m * padicValInt l x := by
  unfold padicValInt
  rw [Int.natAbs_pow, padicValNat.pow]
end Formalism.CohomologicalDescent.UnitNormBounds
