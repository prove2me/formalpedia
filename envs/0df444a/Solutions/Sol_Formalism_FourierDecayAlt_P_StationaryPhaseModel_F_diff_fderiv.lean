-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_diff_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:45.688657+00:00
-- url     : https://prove2.me/submissions/a38bd843-cd92-40ce-b080-4a90f7c6875a

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
theorem _root_.solution (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) :
    DifferentiableOn ℂ (fderiv ℂ g) (Metric.ball 0 (2 * r)) := by
  have h2 : ContDiffOn ℂ ((1 : WithTop ℕ∞) + 1) g (Metric.ball 0 (2 * r)) := by
    have := holo_contDiffOn Metric.isOpen_ball hg 2
    simpa [one_add_one_eq_two] using this
  exact ((contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball).1 h2).2.2.differentiableOn (by simp)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
