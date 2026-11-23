-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.differentiableAt_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:22:31.932861+00:00
-- url     : https://prove2.me/submissions/8d5c5541-778e-4e8f-af50-e6e9ccd932fc

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
theorem _root_.solution {M : ℝ → Matrix l l ℝ} {t : ℝ} (h : ∀ i j, DifferentiableAt ℝ (fun t => M t i j) t) :
    DifferentiableAt ℝ (fun t => (M t).det) t := by
  simp only [Matrix.det_apply']
  exact DifferentiableAt.fun_sum fun σ _ => (DifferentiableAt.fun_finset_prod fun i _ => h _ _).const_mul _
end CompanionTheory.ThKR.LL
