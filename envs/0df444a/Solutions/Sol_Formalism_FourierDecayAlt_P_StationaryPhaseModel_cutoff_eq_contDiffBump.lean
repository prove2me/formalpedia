-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.cutoff_eq_contDiffBump
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:36:18.64872+00:00
-- url     : https://prove2.me/submissions/6de3ce3d-336e-4959-8ce5-64416a90b707

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
theorem _root_.solution (d : ℕ) (ρ : ℝ) (h : 0 < ρ) :
    cutB d ρ = fun x => (⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩ : ContDiffBump (0 : Fin d → ℂ)) x := by
  funext x
  simp [cutB, h]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
