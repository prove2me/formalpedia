-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_cut_smul_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:42.825073+00:00
-- url     : https://prove2.me/submissions/ea192edd-aedd-42eb-9e8d-c41b7bf0d424

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_tsupport

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
variable {d : ℕ} {β : ℂ} {ρ : ℝ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hρ : 0 < ρ) (g : (Fin d → ℂ) → V) :
    tsupport (fun x => cutB d ρ x • g x) ⊆ Metric.closedBall (0 : Fin d → ℂ) ρ :=
  (tsupport_smul_subset_left _ _).trans (E_cut_tsupport hρ).le
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
