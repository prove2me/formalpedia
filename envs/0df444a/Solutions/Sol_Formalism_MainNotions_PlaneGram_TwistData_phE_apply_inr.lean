-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.phE_apply_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:47.625074+00:00
-- url     : https://prove2.me/submissions/349b9f2a-5058-4725-acf6-7f9cda94a1af

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial

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
theorem _root_.solution (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.phE p ζ (Sum.inr t, a) = ζ (D.mlab t, a) + D.P p t * ζ (D.mw t, a) + ζ (D.mtp t, a) := by
  simp [phE, collapseExponent, tpE]
end Formalism.MainNotions.PlaneGram.TwistData
