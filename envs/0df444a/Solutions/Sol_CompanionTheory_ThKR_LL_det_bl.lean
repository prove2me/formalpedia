-- Prove2me | solution 1 for CompanionTheory.ThKR.LL.det_bl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:46.304797+00:00
-- url     : https://prove2.me/submissions/379c31be-690a-4d2e-a093-60158241044d

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
theorem _root_.solution (i j : l → l ⊕ l) (g : Matrix (l ⊕ l) (l ⊕ l) ℝ) : (bl i j g).det = (g.submatrix i j).det :=
  LinearMap.det_toLin (EuclideanSpace.basisFun l ℝ).toBasis _
end CompanionTheory.ThKR.LL
