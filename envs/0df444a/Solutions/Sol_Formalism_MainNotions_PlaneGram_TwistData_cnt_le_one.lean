-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cnt_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:51:25.225849+00:00
-- url     : https://prove2.me/submissions/57677bc9-3c03-4137-8e28-8d5d5c5d5fa5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_eq
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
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) : D.cnt j o i ≤ 1 := by
  by_cases h : ∃ l, D.fk j o l = i
  · obtain ⟨l0, h0⟩ := h
    rw [D.cnt_eq j o i l0 h0]
    split_ifs <;> simp
  · push_neg at h
    rw [D.cnt_zero j o i h]; exact Nat.zero_le _
end Formalism.MainNotions.PlaneGram.TwistData
