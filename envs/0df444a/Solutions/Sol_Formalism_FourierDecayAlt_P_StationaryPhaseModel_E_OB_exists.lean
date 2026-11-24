-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_OB_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:04.438868+00:00
-- url     : https://prove2.me/submissions/3cbffd7d-44a9-4d21-97b6-93a55f69d9d9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_osc_bound

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
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d q : ℕ) (β : ℂ) (hβ : β ≠ 0) (Γ c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ C : ℝ, 0 ≤ C ∧ E_OB d q β Γ c₁ C := osc_bound d q β hβ Γ c₁ hc₁
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
