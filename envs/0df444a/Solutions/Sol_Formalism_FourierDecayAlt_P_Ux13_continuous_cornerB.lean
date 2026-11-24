-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.continuous_cornerB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:27:40.644836+00:00
-- url     : https://prove2.me/submissions/f8de3acf-aed6-4211-9d16-eebb24f439fe

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
theorem _root_.solution {p s : ℕ} : Continuous (cornerB (p := p) (s := s)) := by
  show Continuous fun b : Fin p → Fin s → ℂ => cornerB b
  by_cases h : 0 < s ∧ 0 < p
  · simp only [cornerB, dif_pos h]
    exact continuous_apply_apply _ _
  · simp only [cornerB, dif_neg h]
    exact continuous_const
end Formalism.FourierDecayAlt.P.Ux13
