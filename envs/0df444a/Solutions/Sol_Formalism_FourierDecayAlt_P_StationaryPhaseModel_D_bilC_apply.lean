-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_bilC_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:13:04.746301+00:00
-- url     : https://prove2.me/submissions/c9113752-0437-4d63-b039-0ef07213e5b1

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
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) (x v : Fin d → ℂ) :
    D_bilC d c H Γ hΓ hH x v = (c * (v ⬝ᵥ (H *ᵥ x))).re := rfl
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
