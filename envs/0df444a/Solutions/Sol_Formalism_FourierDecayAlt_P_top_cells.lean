-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.top_cells
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:59:35.116565+00:00
-- url     : https://prove2.me/submissions/4101d5c9-f947-4f5b-a48a-eb819e8ec6c7

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_topCells_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_integrability_top_level
import Theorems.Thm_Formalism_FourierDecayAlt_P_level_z_affine
import Theorems.Thm_Formalism_FourierDecayAlt_P_sizes_top_level


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
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.U.TopCells := by
  exact Formalism.FourierDecayAlt.P.Ux13.topCells_of Formalism.FourierDecayAlt.P.level_z_affine Formalism.FourierDecayAlt.P.sizes_top_level Formalism.FourierDecayAlt.P.integrability_top_level
end Formalism.FourierDecayAlt.P
