-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.UU_dRho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:10.583004+00:00
-- url     : https://prove2.me/submissions/67451c34-85a0-4d44-83f4-ae1fc53278dd

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_Mp_impl_UU
import Theorems.Thm_CompanionTheory_ThKR_Mp_isUnit_UU
import Theorems.Thm_CompanionTheory_ThKF_E_Impl_dRho


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology CompanionTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.Mp
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.Mp
theorem _root_.solution {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (w : l ⊕ l → ℝ) (f : Sch l) :
    UU S t (dRho w f) = dRho (nn S t *ᵥ w) (UU S t f) := by
  have hs : Function.Surjective (UU S t).toLinearMap := fun f => ⟨Ring.inverse (UU S t) f, by
    show (UU S t * Ring.inverse (UU S t)) f = f
    rw [Ring.mul_inverse_cancel _ (isUnit_UU S t), ContinuousLinearMap.one_apply]⟩
  exact Impl.dRho (s := Matrix.mulVecLin (nn S t)) (impl_UU hS t) hs w f
end CompanionTheory.ThKR.Mp
