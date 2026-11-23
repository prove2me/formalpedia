-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_ball_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:35:40.287342+00:00
-- url     : https://prove2.me/submissions/9f0950f7-c2f3-4255-9130-fad63d7e0dc8

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
theorem _root_.solution {x : Fin d → ℂ} {s : ℝ} (hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r) (hs : s ≤ r) :
    Metric.ball x s ⊆ Metric.ball (0 : Fin d → ℂ) (2 * r) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  rw [Metric.mem_ball, dist_zero_right]
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by simpa using norm_add_le (z - x) x
  linarith
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
