-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.liftE_mb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:07:40.605199+00:00
-- url     : https://prove2.me/submissions/c76686d3-64ea-458e-ac6f-ca64a3409006

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial

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
variable (D : TwistData K) (p : ℕ)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (α : D.EA) (b : D.Lb) (a : Fin D.r) : D.liftE p α (D.mb b, a) = α (Sum.inl b, a) := by
  rfl
end Formalism.MainNotions.PlaneGram.TwistData
