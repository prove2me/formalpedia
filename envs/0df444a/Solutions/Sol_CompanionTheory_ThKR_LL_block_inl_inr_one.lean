-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.block_inl_inr_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:06.113637+00:00
-- url     : https://prove2.me/submissions/41158718-dca3-4d49-8ce4-59fa26c1d506

import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_NormExpSubLe
import Definitions.Def_CompanionTheory_ThickeningEstimates_LieGroupReduction_LocalLift
import Theorems.Thm_CompanionTheory_ThKR_LL_bl_apply

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
theorem _root_.solution : bl Sum.inl Sum.inr (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ) = 0 := by
  ext x a
  simp [bl_apply, Matrix.one_apply]
end CompanionTheory.ThKR.LL
