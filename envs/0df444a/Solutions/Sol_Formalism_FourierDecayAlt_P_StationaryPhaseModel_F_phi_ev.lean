-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:22.282386+00:00
-- url     : https://prove2.me/submissions/7eb355bb-afee-4487-9319-b3b334f8651a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_T_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_bump_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (c : ℂ) {x : Fin d → ℂ} (hx : x ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4)) :
    F_phi d r c g =ᶠ[𝓝 x] (realPartMulCLM c ∘ g) := by
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  simp [F_phi, F_bump_one hr (Metric.ball_subset_closedBall hy), F_T_apply]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
