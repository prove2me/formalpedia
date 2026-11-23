-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_clm_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:08.255654+00:00
-- url     : https://prove2.me/submissions/6e5f7fb4-86f8-4460-b7ac-2440e06eebac

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
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {d : ℕ} (L : (Fin d → ℂ) →L[ℂ] ℂ) (v : Fin d → ℂ) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [pi_eq_sum_univ' v]
  simp [map_sum]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
