-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.volJadd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:25.121131+00:00
-- url     : https://prove2.me/submissions/88f573a9-a981-4221-b41d-dcd8496288b3

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Vol_measure_subgroupMatrixSet_mul_card

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
theorem _root_.solution : Formalism.DoubleCosetMeasures.VolJadd := by
  intro F _ _ _ _ _ O hO ϖ hϖ hϖ0 hloc hfin a ν _ J' hK hJ
  haveI := hfin
  exact Vol.measure_subgroupMatrixSet_mul_card O hO ϖ hϖ hϖ0 hloc a ν J' hK hJ
end Formalism.DoubleCosetMeasures.P
