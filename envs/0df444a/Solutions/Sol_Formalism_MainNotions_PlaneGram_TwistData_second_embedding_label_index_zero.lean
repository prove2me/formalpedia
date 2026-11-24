-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.second_embedding_label_index_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:38.545345+00:00
-- url     : https://prove2.me/submissions/680a33c7-4414-4b75-ad01-e826edd2c9a2

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex

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
theorem _root_.solution (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mlab (j, m)) :
    m.val = 0 := by
  revert h
  refine Fin.addCases (fun a => ?_) (fun m0 => ?_) l
  · simp [mb, mlab]
  · rw [second_embedding_natAdd]
    split_ifs with h0
    · intro h
      simp only [mlab, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact h0
    · simp [mlab, mtp]
end Formalism.MainNotions.PlaneGram.TwistData
