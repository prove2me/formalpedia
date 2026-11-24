-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.segL_fk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:17.184952+00:00
-- url     : https://prove2.me/submissions/cfd61582-839f-4acb-bccf-2a5e377dca91

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_segment_letter_first_embedding
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_segment_letter_second_embedding


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
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (l : Fin (D.nB j + D.r)) :
    D.SegL j (D.fk j o l) := by
  unfold fk; split_ifs
  · exact D.segment_letter_second_embedding j l
  · exact D.segment_letter_first_embedding j l
end Formalism.MainNotions.PlaneGram.TwistData
