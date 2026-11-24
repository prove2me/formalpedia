-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.chainSet_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:24.156214+00:00
-- url     : https://prove2.me/submissions/2e1510cf-547b-48a2-b247-0d46ea53dc1a

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
theorem _root_.solution (j : Fin D.J) (i i' : Fin (D.nch j)) (h : D.chain j i ⊆ D.chain j i') :
    D.chainSet j i ⊆ D.chainSet j i' := by
  exact Finset.union_subset_union (Finset.image_subset_image h) (Finset.Subset.refl _)
end Formalism.MainNotions.PlaneGram.TwistData
