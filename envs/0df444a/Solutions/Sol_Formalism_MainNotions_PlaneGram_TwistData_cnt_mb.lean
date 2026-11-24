-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.cnt_mb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:08:27.499099+00:00
-- url     : https://prove2.me/submissions/7179f7ff-63a8-4420-90d7-c59aac7457bd

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fk_castAdd
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_eq

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
    D.cnt j o (D.mb (D.eB j a)) = if Fin.castAdd D.r a ∈ o then 1 else 0 :=
  D.cnt_eq j o _ _ (D.fk_castAdd j o a)
end Formalism.MainNotions.PlaneGram.TwistData
