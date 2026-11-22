-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.pullE_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:05:04.34465+00:00
-- url     : https://prove2.me/submissions/be105131-9ec0-400c-a5ef-897a35a25082

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg

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
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ζ : D.EM) (k : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.pullE j ζ (k, a) = ζ (D.e0 j k, a) := by
  exact Finsupp.comapDomain_apply _ _ _ _
end Formalism.MainNotions.PlaneGram.TwistData
