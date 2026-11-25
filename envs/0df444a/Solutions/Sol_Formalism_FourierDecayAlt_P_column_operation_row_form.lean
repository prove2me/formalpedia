-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.column_operation_row_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:39:15.344678+00:00
-- url     : https://prove2.me/submissions/46119145-fceb-416a-8d80-4635beac8465

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x2_colOp_row

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x2 Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.A5.ColOpRow := by
  intro K _ n Z m c hZ hξ a b
  exact colOp_row Z m c hZ (hξ c le_rfl) a b
end Formalism.FourierDecayAlt.P
