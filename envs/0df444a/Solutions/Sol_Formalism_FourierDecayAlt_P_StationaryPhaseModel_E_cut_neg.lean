-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_cut_neg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:35.763436+00:00
-- url     : https://prove2.me/submissions/4d7c9fb2-4635-4ad0-bd6c-0440eb7a4627

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_neg
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
theorem _root_.solution (hρ : 0 < ρ) (x : Fin d → ℂ) : cutB d ρ (-x) = cutB d ρ x := by
  rw [E_cut_eq hρ]
  exact (E_bump d ρ hρ).neg x
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
