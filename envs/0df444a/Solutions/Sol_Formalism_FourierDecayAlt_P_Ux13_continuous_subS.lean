-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.continuous_subS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:29:22.025534+00:00
-- url     : https://prove2.me/submissions/7111a469-e0c4-4eb9-bf04-08e23be1ad09

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
theorem _root_.solution {p : ℕ} : Continuous (subS (p := p)) := by
  show Continuous fun l : Matrix (Fin p) (Fin p) ℂ => subS l
  unfold subS
  refine continuous_finset_sum _ fun i _ => ?_
  by_cases h : i.val + 1 < p
  · simp only [dif_pos h]
    exact continuous_id.matrix_elem _ _
  · simp only [dif_neg h]
    exact continuous_const
end Formalism.FourierDecayAlt.P.Ux13
