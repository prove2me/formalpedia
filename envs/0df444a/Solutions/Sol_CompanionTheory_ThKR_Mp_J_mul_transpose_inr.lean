-- Prove2me | solution 1 for CompanionTheory.ThKR.Mp.J_mul_transpose_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:21:25.738681+00:00
-- url     : https://prove2.me/submissions/1857927f-abcb-489b-8867-5336ebd86555

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_ContinuousOm
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_MetaplecticRepresentation_MetaplecticUnipotentBlockSecondDiag

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
theorem _root_.solution (s : Mat l) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inr a) j = s j (.inl a) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
end CompanionTheory.ThKR.Mp
