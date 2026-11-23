-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.emb_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:12.982533+00:00
-- url     : https://prove2.me/submissions/47976b7f-fe89-46b2-9c56-a7edb42e91c1

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
theorem _root_.solution (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.emb p ρ ζ (Sum.inl b, a) = ζ (D.mb b, a) := by
  rfl
end Formalism.MainNotions.PlaneGram.TwistData
