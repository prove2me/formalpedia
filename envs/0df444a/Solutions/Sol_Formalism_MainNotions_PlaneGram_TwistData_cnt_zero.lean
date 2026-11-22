-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cnt_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:28:43.488869+00:00
-- url     : https://prove2.me/submissions/7afdffad-9925-459f-8705-bf56d4019b60

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
theorem _root_.solution (o : Finset (Fin (D.nB j + D.r))) (i : D.ML) (h : ∀ l, D.fk j o l ≠ i) :
    D.cnt j o i = 0 := by
  unfold cnt
  exact Finset.sum_eq_zero fun l _ => if_neg (h l)
end Formalism.MainNotions.PlaneGram.TwistData
