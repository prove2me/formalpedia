-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.PsiP_HomD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:24.763563+00:00
-- url     : https://prove2.me/submissions/78c16440-eed8-4593-86fd-52a5388594a6

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_fk_inj
import Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_prod
import Theorems.Thm_Formalism_MainNotions_PlaneGram_HomD_rename
import Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_PolK_iff


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
theorem _root_.solution {nc : ℕ} (col : Fin nc → MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K)
    (occ : Fin nc → Finset (Fin (D.nB j + D.r)))
    (hcol : ∀ k, col k ∈ PolK K D.r (fun i => if i ∈ occ k then 1 else 0)) :
    HomD (fun i => ∑ k, D.cnt j (occ k) i) (D.PsiP j col occ) := by
  unfold PsiP
  refine HomD_prod _ _ _ fun k _ => ?_
  exact HomD_rename (D.fk j (occ k)) (D.fk_inj j _) _ _ ((mem_PolK_iff _ _).mp (hcol k))
end Formalism.MainNotions.PlaneGram.TwistData
