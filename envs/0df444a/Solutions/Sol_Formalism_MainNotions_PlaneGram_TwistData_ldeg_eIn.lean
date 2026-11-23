-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ldeg_eIn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:13.73672+00:00
-- url     : https://prove2.me/submissions/11a88b8d-d245-4c94-a9a8-c9b77996b116

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
theorem _root_.solution (ζ : D.EM) (i : D.ML) : ldeg (eIn D.outP ζ) i = if D.outP i then 0 else ldeg ζ i := by
  unfold ldeg eIn
  split_ifs with h
  · simp [Finsupp.filter_apply, h]
  · have h' : D.outB i = false := by simpa [outP] using h
    simp [Finsupp.filter_apply, h']
end Formalism.MainNotions.PlaneGram.TwistData
