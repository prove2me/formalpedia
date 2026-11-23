-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_phi_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:16.925567+00:00
-- url     : https://prove2.me/submissions/c19983f0-d331-4e37-bd50-ab9518d74153

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_contDiff_mul_cut
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_bump_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_bump_tsupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_g_contDiffOn

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
theorem _root_.solution (hr : 0 < r) (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) (n : ℕ) :
    ContDiff ℝ n (F_phi d r c g) := by
  refine F_contDiff_mul_cut Metric.isOpen_ball (F_bump_contDiff hr n) (F_bump_tsupport hr) ?_
  exact (realPartMulCLM c).contDiff.comp_contDiffOn (F_g_contDiffOn hg n)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
