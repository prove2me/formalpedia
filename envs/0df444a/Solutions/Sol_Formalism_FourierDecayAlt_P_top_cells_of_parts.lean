-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.top_cells_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:51:52.840362+00:00
-- url     : https://prove2.me/submissions/cddec2ec-db2d-49e9-ab67-46082b520571

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_topCellsOfParts

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
theorem _root_.solution : Formalism.FourierDecayAlt.U.TopCellsOfParts := by
  exact Formalism.FourierDecayAlt.P.Ux13.topCellsOfParts
end Formalism.FourierDecayAlt.P
