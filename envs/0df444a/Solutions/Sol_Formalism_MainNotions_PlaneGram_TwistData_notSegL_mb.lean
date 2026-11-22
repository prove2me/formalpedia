-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.notSegL_mb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:43.329152+00:00
-- url     : https://prove2.me/submissions/d5e6aaab-4614-4280-b34f-2c6faa6a873d

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
theorem _root_.solution {j : Fin D.J} {b : D.Lb} (h : D.seg b ≠ j) : ¬ D.SegL j (D.mb b) := by
  rintro (⟨b', h1, e⟩ | ⟨m, e⟩ | ⟨m, e⟩)
  · simp only [mb, Sum.inl.injEq] at e
    exact h (e ▸ h1)
  · simp [mb, mlab] at e
  · simp [mb, mtp] at e
end Formalism.MainNotions.PlaneGram.TwistData
