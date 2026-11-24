-- Prove2me | solution 1 for Formalism.MainNotions.Inhab.subst_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:40:17.421073+00:00
-- url     : https://prove2.me/submissions/a443d0bc-10fb-405f-b2ba-a0622c7b6cf5

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_SharpRestriction_InertJacobiLevels_ExtraGat
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Inhab
open Formalism.MainNotions.G MvPolynomial
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
variable (P : Places p O Kf)
namespace Formalism.MainNotions.Inhab
theorem _root_.solution : P.subst (fun _ _ => 1) = AlgHom.id Kf P.Xsp := by
  apply MvPolynomial.algHom_ext
  rintro ⟨v, s, a, t⟩
  simp only [Places.subst, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [Matrix.one_apply_ne (Ne.symm hb)]; simp
  · intro h; exact absurd (Finset.mem_univ _) h
end Formalism.MainNotions.Inhab
