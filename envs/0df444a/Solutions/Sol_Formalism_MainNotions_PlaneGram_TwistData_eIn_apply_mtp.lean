-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.eIn_apply_mtp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:51:15.314998+00:00
-- url     : https://prove2.me/submissions/0fa54140-88d4-4ad0-beb9-c2b58b38de98

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
import Theorems.Thm_Formalism_MainNotions_PlaneGram_eIn_apply


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
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mtp t, a) = 0 := by
  rw [eIn_apply]
  simp [outP, outB, mtp]
end Formalism.MainNotions.PlaneGram.TwistData
