-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.UU_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:19:55.908058+00:00
-- url     : https://prove2.me/submissions/5b4cb8e1-40be-4cb8-b964-e91e3c4a3deb

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag
import Theorems.Thm_CompanionTheory_ThKR_LL_fou_mul_fouInv
import Theorems.Thm_CompanionTheory_ThKR_LL_ph_zero


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
theorem _root_.solution (S : Matrix l l ℝ) : UU S 0 = 1 := by
  simp [UU, ph_zero, fou_mul_fouInv]
end CompanionTheory.ThKR.Mp
