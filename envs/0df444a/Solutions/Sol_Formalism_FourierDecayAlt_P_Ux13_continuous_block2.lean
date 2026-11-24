-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux13.continuous_block2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:27:28.105733+00:00
-- url     : https://prove2.me/submissions/4dd34447-9117-4a54-94d3-7a65c4971cfd

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
theorem _root_.solution {α : Type*} [TopologicalSpace α] {p s : ℕ} {A : α → Matrix (Fin p) (Fin p) ℂ}
    {B : α → Matrix (Fin p) (Fin s) ℂ} {C : α → Matrix (Fin s) (Fin p) ℂ} {D : α → Matrix (Fin s) (Fin s) ℂ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => blk2 (A x) (B x) (C x) (D x) := by
  exact (hA.matrix_fromBlocks hB hC hD).matrix_reindex _ _
end Formalism.FourierDecayAlt.P.Ux13
