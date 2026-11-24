-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.YP_preimage0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:50:54.121112+00:00
-- url     : https://prove2.me/submissions/b7a77513-fef7-45b0-a8ce-85f140eb0ad9

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_IntegralMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective

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
theorem _root_.solution (m : Fin D.r) (k : Fin (D.nB j + D.r))
    (hk : k ∈ (D.YPset j m).preimage (D.e0 j) (D.index_embedding_injective j).injOn) : k.val < D.nB j := by
  rw [Finset.mem_preimage] at hk
  induction k using Fin.addCases with
  | left a => simp
  | right m' =>
    rw [first_embedding_natAdd] at hk
    simp [YPset, mb, mlab, mtp] at hk
end Formalism.MainNotions.PlaneGram.TwistData
