-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.continuous_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:26:03.876822+00:00
-- url     : https://prove2.me/submissions/36e32585-446d-4378-99ee-2190e4a48e5c

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
namespace Formalism.FourierDecayAlt.P.Ux13
theorem _root_.solution {p : ℕ} : Continuous (G.upper (d := p)) := by
  refine continuous_matrix fun a b => ?_
  by_cases h : a < b
  · simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_pos h]
    exact continuous_const.add (continuous_apply _)
  · simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_neg h]
    exact continuous_const
end Formalism.FourierDecayAlt.P.Ux13
