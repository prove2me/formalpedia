-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.C_line_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:26.465049+00:00
-- url     : https://prove2.me/submissions/bf387ece-842c-4432-af9d-9acf14e37a1e

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
open MeasureTheory Filter Topology Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {f : E → F} {y v : E} {ζ : ℂ} (h : DifferentiableAt ℂ f (y + ζ • v)) :
    HasDerivAt (fun z : ℂ => f (y + z • v)) (fderiv ℂ f (y + ζ • v) v) ζ := by
  have h1 : HasDerivAt (fun z : ℂ => y + z • v) v ζ := by
    simpa using ((hasDerivAt_id ζ).smul_const v).const_add y
  exact h.hasFDerivAt.comp_hasDerivAt ζ h1
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
