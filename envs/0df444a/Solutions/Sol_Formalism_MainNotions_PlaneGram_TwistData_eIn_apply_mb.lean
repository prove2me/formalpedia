-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.eIn_apply_mb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:51:12.022447+00:00
-- url     : https://prove2.me/submissions/65a2ca29-663a-4d19-a12b-ae5c48178922

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
theorem _root_.solution (ζ : D.EM) (b : D.Lb) (a : Fin D.r) : eIn D.outP ζ (D.mb b, a) = ζ (D.mb b, a) := by
  rw [eIn_apply]
  simp [outP, outB, mb]
end Formalism.MainNotions.PlaneGram.TwistData
