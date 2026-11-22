-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.notSegL_mtp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:04:44.354856+00:00
-- url     : https://prove2.me/submissions/d1c3b7ca-a04c-419c-b7cd-614fbfb93e66

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
theorem _root_.solution {j j' : Fin D.J} (m : Fin D.r) (h : j' ≠ j) : ¬ D.SegL j (D.mtp (j', m)) := by
  rintro (⟨b', h1, e⟩ | ⟨m', e⟩ | ⟨m', e⟩)
  · simp [mb, mtp] at e
  · simp [mlab, mtp] at e
  · simp only [mtp, Sum.inr.injEq, Prod.mk.injEq] at e
    exact h e.1
end Formalism.MainNotions.PlaneGram.TwistData
