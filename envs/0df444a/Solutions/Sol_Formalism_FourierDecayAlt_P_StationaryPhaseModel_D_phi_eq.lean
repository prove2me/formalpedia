-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_phi_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:43.802809+00:00
-- url     : https://prove2.me/submissions/dbbabbf1-48e2-4910-97a5-aaaecd352abc

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_bilC_apply

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
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) : D_phi d c H = fun x => (1 / 2 : ℝ) * D_bilC d c H Γ hΓ hH x x := by
  funext x
  rw [D_bilC_apply, D_phi, ← Complex.re_ofReal_mul]
  congr 1
  push_cast
  ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
