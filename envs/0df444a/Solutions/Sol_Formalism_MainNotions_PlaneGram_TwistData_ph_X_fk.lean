-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ph_X_fk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:30.405444+00:00
-- url     : https://prove2.me/submissions/33f6f206-3afe-4d35-91ef-c49fc2621d0b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding

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
theorem _root_.solution (p : ℕ) (o : Finset (Fin (D.nB j + D.r))) (l : Fin (D.nB j + D.r)) (a : Fin D.r) :
    D.ph p (X (D.fk j o l, a) : MvPolynomial (D.ML × Fin D.r) K) = X (D.eA j l, a) := by
  unfold fk ph
  rw [aeval_X]
  refine Fin.addCases (fun a0 => ?_) (fun m => ?_) l
  · split_ifs <;> simp [mb]
  · split_ifs
    · rw [second_embedding_natAdd]
      split_ifs <;> simp [mlab, mtp]
    · simp [mlab]
end Formalism.MainNotions.PlaneGram.TwistData
