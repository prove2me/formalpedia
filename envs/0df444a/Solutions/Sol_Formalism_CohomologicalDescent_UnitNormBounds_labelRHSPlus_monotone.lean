-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.labelRHSPlus_monotone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:14:37.530853+00:00
-- url     : https://prove2.me/submissions/34d49a6d-b719-4051-b8b0-8213641f8cc5

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_harmonic_monotone
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_gated_min_monotone

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
theorem _root_.solution (l k t h : ℕ) (xm xp mB : ℤ) {a b : ℝ} (hab : a ≤ b) :
    labelSumBoundPos l k t h a xm xp mB ≤ labelSumBoundPos l k t h b xm xp mB := by
  unfold labelSumBoundPos
  have h1 := gated_min_monotone l k t (xm - mB) hab
  have h2 := harmonic_monotone l h hab
  linarith
end Formalism.CohomologicalDescent.UnitNormBounds
