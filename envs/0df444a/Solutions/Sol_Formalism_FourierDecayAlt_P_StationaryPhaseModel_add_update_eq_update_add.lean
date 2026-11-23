-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.add_update_eq_update_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:02.466341+00:00
-- url     : https://prove2.me/submissions/70be8481-2f1c-49fb-a8d3-076e21f0386f

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
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {d : ℕ} (x₀ x : Fin d → ℂ) (k : Fin d) (ξ : ℂ) :
    x₀ + Function.update x k ξ = Function.update (x₀ + x) k (x₀ k + ξ) := by
  ext i
  by_cases h : i = k
  · subst h; simp
  · simp [h]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
