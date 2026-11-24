-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cnt_lab_add_tp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:36.110604+00:00
-- url     : https://prove2.me/submissions/30416bed-4bd7-4fa8-b1c6-e888b9447109

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_eq
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_first_embedding_ne_tangent
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_second_embedding_tangent_index
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_second_embedding_label_index_zero

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
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) :
    D.cnt j o (D.mlab (j, m)) + D.cnt j o (D.mtp (j, m)) =
      if Fin.natAdd (D.nB j) (Fin.rev m) ∈ o then 1 else 0 := by
  by_cases hM : D.Marked j o
  · have hf : D.fk j o = D.e1 j := by unfold fk; rw [if_pos hM]
    by_cases h0 : m.val = 0
    · rw [D.cnt_eq j o (D.mlab (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, second_embedding_natAdd, Fin.rev_rev, if_pos h0]),
        D.cnt_zero j o (D.mtp (j, m)) (by
          intro l hl; rw [hf] at hl; exact (D.second_embedding_tangent_index j l m hl).1 h0), add_zero]
    · rw [D.cnt_eq j o (D.mtp (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, second_embedding_natAdd, Fin.rev_rev, if_neg h0]),
        D.cnt_zero j o (D.mlab (j, m)) (by
          intro l hl; rw [hf] at hl; exact h0 (D.second_embedding_label_index_zero j l m hl)), zero_add]
  · have hf : D.fk j o = D.e0 j := by unfold fk; rw [if_neg hM]
    rw [D.cnt_eq j o (D.mlab (j, m)) (Fin.natAdd (D.nB j) (Fin.rev m))
        (by rw [hf, first_embedding_natAdd, Fin.rev_rev]),
        D.cnt_zero j o (D.mtp (j, m)) (by
          intro l hl; rw [hf] at hl; exact D.first_embedding_ne_tangent j l _ hl), add_zero]
end Formalism.MainNotions.PlaneGram.TwistData
