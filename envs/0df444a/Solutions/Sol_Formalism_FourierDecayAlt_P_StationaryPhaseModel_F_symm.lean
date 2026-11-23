-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_symm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:35.088148+00:00
-- url     : https://prove2.me/submissions/67a27a2e-fdad-4c43-9f2f-9323b95a97dc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_holo_contDiffOn

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
variable {d : ℕ} {r : ℝ} {g : (Fin d → ℂ) → ℂ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (u v : Fin d → ℂ) :
    fderiv ℂ (fderiv ℂ g) 0 u v = fderiv ℂ (fderiv ℂ g) 0 v u := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have h2 : ContDiffAt ℂ (2 : ℕ) g 0 :=
    (holo_contDiffOn Metric.isOpen_ball hg 2).contDiffAt (Metric.isOpen_ball.mem_nhds h0)
  exact h2.isSymmSndFDerivAt (by simp) u v
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
