-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.label_function_same_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:13.548777+00:00
-- url     : https://prove2.me/submissions/d666303b-233c-40cf-8842-c234afb10872

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory

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
theorem _root_.solution {ζ ζ' : D.EM} (hb : D.SameBlockAlt ζ ζ') : D.labF ζ' = D.labF ζ := by
  unfold SameBlockAlt at hb
  obtain ⟨_, hlab, _⟩ := hb
  funext t a
  exact hlab t a
end Formalism.MainNotions.PlaneGram.TwistData
