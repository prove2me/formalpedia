-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_cut_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:44.451823+00:00
-- url     : https://prove2.me/submissions/efc3c27f-dcdc-4b19-80e3-b16cd2c18f61

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_eq

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
variable {d : ℕ} {ρ : ℝ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hρ : 0 < ρ) : tsupport (cutB d ρ) = Metric.closedBall (0 : Fin d → ℂ) ρ := by
  rw [E_cut_eq hρ]
  exact (E_bump d ρ hρ).tsupport_eq
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
