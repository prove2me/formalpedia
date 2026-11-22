-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.phE_apply_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:03:59.906523+00:00
-- url     : https://prove2.me/submissions/6d9434d7-5327-4400-b3bf-94a7fab9b7e6

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
theorem _root_.solution (p : ℕ) (ζ : D.EM) (b : D.Lb) (a : Fin D.r) :
    D.phE p ζ (Sum.inl b, a) = ζ (D.mb b, a) := by
  simp [phE, collapseExponent, tpE]
end Formalism.MainNotions.PlaneGram.TwistData
