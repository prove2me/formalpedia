-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_hasFDerivAt_Tg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:01.060212+00:00
-- url     : https://prove2.me/submissions/7b13e0a7-cd00-493c-b4f8-5d760dcd8c7f

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
theorem _root_.solution (hg : DifferentiableOn ℂ g (Metric.ball 0 (2 * r))) (c : ℂ) {x : Fin d → ℂ}
    (hx : x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r)) :
    HasFDerivAt (realPartMulCLM c ∘ g) ((realPartMulCLM c).comp ((fderiv ℂ g x).restrictScalars ℝ)) x :=
  (realPartMulCLM c).hasFDerivAt.comp x
    ((hg.differentiableAt (Metric.isOpen_ball.mem_nhds hx)).hasFDerivAt.restrictScalars ℝ)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
