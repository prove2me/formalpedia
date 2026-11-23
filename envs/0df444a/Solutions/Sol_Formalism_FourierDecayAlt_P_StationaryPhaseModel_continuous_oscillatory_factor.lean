-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.continuous_oscillatory_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:22.940078+00:00
-- url     : https://prove2.me/submissions/adef8646-b3f7-4406-aafc-792527198a8c

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
variable {d : ℕ} {β : ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {E : Type*} [TopologicalSpace E] {φ : E → ℝ} (hφ : Continuous φ) (τ : ℝ) :
    Continuous (osc φ τ) := by
  unfold osc
  fun_prop
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
