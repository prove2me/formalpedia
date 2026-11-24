-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cnt_tp_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:26.538893+00:00
-- url     : https://prove2.me/submissions/7940ec3c-f018-4adc-97aa-afbf3321d075

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_first_embedding_ne_tangent
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_second_embedding_tangent_index

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
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) (h0 : m.val = 0) :
    D.cnt j o (D.mtp (j, m)) = 0 := by
  apply D.cnt_zero
  intro l hl
  unfold fk at hl
  split_ifs at hl
  · exact (D.second_embedding_tangent_index j l m hl).1 h0
  · exact D.first_embedding_ne_tangent j l _ hl
end Formalism.MainNotions.PlaneGram.TwistData
