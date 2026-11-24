-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cnt_not_segL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:40:58.986267+00:00
-- url     : https://prove2.me/submissions/4aac479e-0e2d-4357-b63b-05c1246b26c8

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_segL_fk
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_zero

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
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (hi : ¬ D.SegL j i) :
    D.cnt j o i = 0 := by
  apply D.cnt_zero
  intro l hl
  exact hi (hl ▸ D.segL_fk j o l)
end Formalism.MainNotions.PlaneGram.TwistData
