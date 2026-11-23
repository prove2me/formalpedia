-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.second_embedding_tangent_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:15.901687+00:00
-- url     : https://prove2.me/submissions/d7d1efb3-520a-4108-901e-dcca15bdd987

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
theorem _root_.solution (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mtp (j, m)) :
    m.val ≠ 0 ∧ l = Fin.natAdd (D.nB j) (Fin.rev m) := by
  revert h
  refine Fin.addCases (fun a => ?_) (fun m0 => ?_) l
  · simp [mb, mtp]
  · rw [second_embedding_natAdd]
    split_ifs with h0
    · simp [mlab, mtp]
    · intro h
      simp only [mtp, Sum.inr.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact ⟨h0, by rw [Fin.rev_rev]⟩
end Formalism.MainNotions.PlaneGram.TwistData
