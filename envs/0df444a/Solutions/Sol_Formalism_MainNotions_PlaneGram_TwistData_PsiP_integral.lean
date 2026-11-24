-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.PsiP_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:10:48.341624+00:00
-- url     : https://prove2.me/submissions/de9df90a-64fb-4f67-a27c-a3b2e2e6fa65

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fk_inj
import Theorems.Thm_Formalism_MainNotions_PlaneGram_integral_prod_rename


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
theorem _root_.solution {v : AddValuation K (WithTop ℚ)} {nc : ℕ}
    (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r))) (h : Integral v (∏ k, col k)) :
    Integral v (D.PsiP j col occ) :=
  integral_prod_rename col (fun k => Prod.map (D.fk j (occ k)) id)
    (fun k => (D.fk_inj j (occ k)).prodMap Function.injective_id) h
end Formalism.MainNotions.PlaneGram.TwistData
