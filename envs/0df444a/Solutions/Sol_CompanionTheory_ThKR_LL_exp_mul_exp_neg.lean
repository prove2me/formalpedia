-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.exp_mul_exp_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:46.882588+00:00
-- url     : https://prove2.me/submissions/3419c9b9-1229-46b0-b09f-04d9e38f3c5b

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil CompanionTheory.ThKF.E Filter Topology LineDeriv
open scoped Real RealInnerProductSpace FourierTransform
open CompanionTheory CompanionTheory.ThKR CompanionTheory.ThKR.LL
variable {l : Type} [Fintype l] [DecidableEq l]
namespace CompanionTheory.ThKR.LL
theorem _root_.solution (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute _ _ (Commute.refl X).neg_right, add_neg_cancel, NormedSpace.exp_zero]
end CompanionTheory.ThKR.LL
