-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.splitE_mlab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:44.706398+00:00
-- url     : https://prove2.me/submissions/599ad2bf-b1b1-43d4-98fe-0bc78a8c1e31

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin

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
theorem _root_.solution (p : ℕ) (ζ : D.EM) (t : D.Tau) (a : Fin D.r) :
    D.splitE p ζ (D.mlab t, a) = ζ (D.mlab t, a) % D.P p t := by simp [splitE, mlab]
end Formalism.MainNotions.PlaneGram.TwistData
