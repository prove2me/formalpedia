-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ph_rename_fk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:15.074461+00:00
-- url     : https://prove2.me/submissions/90c6de39-d6a6-4dda-b3da-b54a9d78513a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_X_fk

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
theorem _root_.solution (p : ℕ) (o : Finset (Fin (D.nB j + D.r)))
    (G : MvPolynomial (Fin (D.nB j + D.r) × Fin D.r) K) :
    D.ph p (rename (Prod.map (D.fk j o) id) G) = rename (Prod.map (D.eA j) id) G := by
  have : (D.ph p).comp (rename (Prod.map (D.fk j o) (id : Fin D.r → Fin D.r))) =
      rename (Prod.map (D.eA j) (id : Fin D.r → Fin D.r)) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨l, a⟩
    simp only [AlgHom.comp_apply, rename_X, Prod.map_apply, id_eq]
    exact D.ph_X_fk j p o l a
  exact DFunLike.congr_fun this G
end Formalism.MainNotions.PlaneGram.TwistData
