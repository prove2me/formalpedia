-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:22.3478+00:00
-- url     : https://prove2.me/submissions/f1901902-b1d6-473f-b2c0-11624c67c8c1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel

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
theorem _root_.solution (hr : 0 < r) {x : Fin d → ℂ} (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) :
    x ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4) := by
  rw [Metric.mem_closedBall] at hx
  rw [Metric.mem_ball]
  linarith
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
