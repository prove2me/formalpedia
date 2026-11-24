-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.eIn_apply_mlab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:51:13.472978+00:00
-- url     : https://prove2.me/submissions/0282b969-72d3-4584-b5f6-3604e7380d72

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
theorem _root_.solution (ζ : D.EM) (t : D.Tau) (a : Fin D.r) : eIn D.outP ζ (D.mlab t, a) = 0 := by
  rw [eIn_apply]
  simp [outP, outB, mlab]
end Formalism.MainNotions.PlaneGram.TwistData
