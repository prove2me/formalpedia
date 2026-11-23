-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.volII
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:11.699932+00:00
-- url     : https://prove2.me/submissions/4d72d169-ec4e-430a-84b1-62ff6c5663a6

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measure_uniformizerMatrixSet_mul_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : Formalism.DoubleCosetMeasures.VolII := by
  intro F _ _ _ _ _ O hO ϖ hϖ hϖ0 hfin n a ν _
  haveI := hfin
  exact Vol.measure_uniformizerMatrixSet_mul_card O hO ϖ hϖ hϖ0 n a ν
end Formalism.DoubleCosetMeasures.P
