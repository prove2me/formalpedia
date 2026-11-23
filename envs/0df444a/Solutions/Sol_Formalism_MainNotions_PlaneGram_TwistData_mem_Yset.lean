-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.mem_Yset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:14.301895+00:00
-- url     : https://prove2.me/submissions/32d2ad51-0206-4a83-b58a-eb389f68d107

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (j : Fin D.J) (m : Fin D.r) (z : D.ML) :
    z ∈ D.Yset j m ↔ (∃ m' : Fin D.r, D.mw (D.aux₃ j, m') = z) ∨ (∃ b ∈ D.LLj j, D.mb b = z) ∨
      ∃ m' : Fin D.r, m < m' ∧ D.mtp (j, m') = z := by
  simp [Yset, wSet, or_assoc]
end Formalism.MainNotions.PlaneGram.TwistData
