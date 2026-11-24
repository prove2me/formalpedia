-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.fk_castAdd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:52:58.038304+00:00
-- url     : https://prove2.me/submissions/d68f716b-a2e6-48d5-8622-e1a6b2d456d4

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
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (a : Fin (D.nB j)) :
    D.fk j o (Fin.castAdd D.r a) = D.mb (D.eB j a) := by
  unfold fk; split_ifs <;> simp
end Formalism.MainNotions.PlaneGram.TwistData
