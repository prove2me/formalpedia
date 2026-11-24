-- Prove2me | solution 1 for Formalism.MainNotions.Inhab.levAll_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:06:56.128808+00:00
-- url     : https://prove2.me/submissions/6a75760c-649c-4e8a-bb07-df2999171626

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat
import Theorems.Thm_Formalism_MainNotions_Inhab_map_colSpan
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.MainNotions.G MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
variable (P : Places p O Kf)
namespace Formalism.MainNotions.Inhab
theorem _root_.solution (L L' : P.Tup) (hL : P.IsLatTup L) (hL' : P.IsLatTup L') :
    ∃ γ : (levAll P).Γ, L' = (levAll P).smul γ L := by
  choose g hg hgL using hL
  choose g' hg' hgL' using hL'
  refine ⟨((fun v => Matrix.GeneralLinearGroup.mk'' (g' v * (g v)⁻¹) (by
    rw [Matrix.det_mul]; exact (hg' v).mul (Matrix.isUnit_nonsing_inv_det _ (hg v)))), 1), ?_⟩
  funext v
  show L' v = (L v).map ((Matrix.mulVecLin (g' v * (g v)⁻¹)).restrictScalars (P.W v))
  rw [hgL v, hgL' v, map_colSpan, Matrix.nonsing_inv_mul_cancel_right _ _ (hg v)]
end Formalism.MainNotions.Inhab
