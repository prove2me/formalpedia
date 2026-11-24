-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.rowStart_rev_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:03:37.848574+00:00
-- url     : https://prove2.me/submissions/fae5a71a-472f-476b-b9a3-4b9b120a0267

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds

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
theorem _root_.solution (k j t w M : ℕ) (lam : Fin (k + j) → ℕ) (hb : ∀ a, w ≤ lam a ∧ lam a ≤ M)
    (b : Fin (k + j)) :
    U k j t lam (Fin.rev b) = (M : ℤ) - (dual M lam b : ℤ) + (t : ℤ) + (b.val : ℤ) := by
  have h1 := Fin.val_rev b
  have h2 := hb (Fin.rev b)
  have h3 := b.isLt
  unfold U dual
  omega
end Formalism.CohomologicalDescent.UnitNormBounds
