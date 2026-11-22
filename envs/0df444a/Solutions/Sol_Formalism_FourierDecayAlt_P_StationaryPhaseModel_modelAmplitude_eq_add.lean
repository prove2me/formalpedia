-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.modelAmplitude_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:15:08.794825+00:00
-- url     : https://prove2.me/submissions/5e1d74bf-1fa0-4a3d-9fc3-807fefaaa132

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
variable {d : ℕ} {β : ℂ} {ρ : ℝ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (a₀ : V) (ℓ : (Fin d → ℂ) →L[ℝ] V) :
    modelAmplitude d ρ a₀ ℓ = fun x => constantAmplitude d ρ a₀ x + linearAmplitude d ρ ℓ x := by
  funext x
  simp [modelAmplitude, constantAmplitude, linearAmplitude, smul_add]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
