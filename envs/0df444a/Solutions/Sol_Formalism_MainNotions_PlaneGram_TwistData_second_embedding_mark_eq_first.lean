-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.second_embedding_mark_eq_first
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:39.830941+00:00
-- url     : https://prove2.me/submissions/4e834725-a6e9-4c72-be18-5e61b700b247

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
theorem _root_.solution (k : Fin (D.nB j + D.r)) : D.msg (D.e1 j k) = D.msg (D.e0 j k) := by
  induction k using Fin.addCases with
  | left a => simp
  | right m =>
    simp only [second_embedding_natAdd, first_embedding_natAdd]
    split_ifs <;> simp [msg, mlab, mtp]
end Formalism.MainNotions.PlaneGram.TwistData
