-- Prove2me | solution 1 for Formalism.CohomologicalDescent.UnitNormBounds.labelRHSPlus_shift_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:16:14.699235+00:00
-- url     : https://prove2.me/submissions/f21b857e-986c-4d76-87ba-6524e265300a

import Definitions.Def_Formalism_PieriBlockIdeals_FactorialValuationSum
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Theorems.Thm_Formalism_CohomologicalDescent_UnitNormBounds_indexIntegral_shift

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
theorem _root_.solution (l k t h : ℕ) (I : ℝ) (xm xp mB c : ℤ) :
    labelSumBoundPos l k t h I (xm + c) (xp + c) (mB + c) = labelSumBoundPos l k t h I xm xp mB := by
  unfold labelSumBoundPos
  have e1 : xp + c - (xm + c) = xp - xm := by ring
  have e2 : xm + c - (mB + c) = xm - mB := by ring
  have e3 : xp + c - (mB + c) = xp - mB := by ring
  have e4 : IlInd l (xm + c) (xp + c) (mB + c) = IlInd l xm xp mB := by
    rw [← indexIntegral_shift l (xm + c) (xp + c) (mB + c), e2, e3, indexIntegral_shift]
  rw [e1, e2, e4]
end Formalism.CohomologicalDescent.UnitNormBounds
