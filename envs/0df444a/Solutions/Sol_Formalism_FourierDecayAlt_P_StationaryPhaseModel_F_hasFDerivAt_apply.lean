-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_hasFDerivAt_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:16.848918+00:00
-- url     : https://prove2.me/submissions/ca1a1a71-5e29-4ed3-acb6-9e9c5e3e2568

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_diff_fderiv

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
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (v : Fin d → ℂ) :
    HasFDerivAt (fun y => fderiv ℂ g y v)
      ((ContinuousLinearMap.apply ℂ ℂ v).comp (fderiv ℂ (fderiv ℂ g) 0)) 0 := by
  have h0 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have hB : HasFDerivAt (fderiv ℂ g) (fderiv ℂ (fderiv ℂ g) 0) 0 :=
    ((F_diff_fderiv hg).differentiableAt (Metric.isOpen_ball.mem_nhds h0)).hasFDerivAt
  exact (ContinuousLinearMap.apply ℂ ℂ v).hasFDerivAt.comp 0 hB
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
