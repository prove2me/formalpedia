-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.B_contDiff_osc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:27.048388+00:00
-- url     : https://prove2.me/submissions/26024aa1-9607-4e8c-bb98-5cc352512824

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
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {φ : E → ℝ} (τ : ℝ) {n : ℕ} (hφ : ContDiff ℝ n φ) : ContDiff ℝ n (osc φ τ) := by
  unfold osc
  have h1 : ContDiff ℝ n (fun y => ((φ y / τ : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hφ.div_const τ)
  exact (contDiff_const.mul h1).cexp
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
