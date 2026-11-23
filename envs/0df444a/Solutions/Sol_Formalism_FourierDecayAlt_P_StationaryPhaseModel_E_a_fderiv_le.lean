-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_a_fderiv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:35.675798+00:00
-- url     : https://prove2.me/submissions/62a72935-6fc1-4ef2-beb2-5f3206fc2c98

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
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {a : (Fin d → ℂ) → V} (hbd : ∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) :
    ‖fderiv ℝ a 0‖ ≤ S := by
  rw [← norm_iteratedFDeriv_one]
  exact hbd 1 (by omega) 0
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
