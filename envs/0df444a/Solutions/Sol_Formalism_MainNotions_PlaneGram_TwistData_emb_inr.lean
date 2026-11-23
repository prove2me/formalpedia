-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.emb_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:13.067589+00:00
-- url     : https://prove2.me/submissions/7f9a364c-b8ae-4ce7-8104-e06f6f62c51e

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
theorem _root_.solution (ρ : D.Tau → Fin D.r → ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.emb p ρ ζ (Sum.inr t, a) = ρ t a + D.P p t * ζ (D.mw t, a) := by
  rfl
end Formalism.MainNotions.PlaneGram.TwistData
