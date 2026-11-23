-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HLsc.integrable_indicator_cube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:53.30718+00:00
-- url     : https://prove2.me/submissions/d4a024be-b171-46ca-92c1-f9e6528fddc5

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HerglotzLowerSemicontinuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_isCompact_cube
import Theorems.Thm_Formalism_FourierDecayAlt_P_HLsc_measurableSet_cube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HLsc
open Real Filter Topology Finset MeasureTheory Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.HLsc
theorem _root_.solution : Integrable ((cube d).indicator (fun _ => (1 : ℝ))) := by
  rw [integrable_indicator_iff measurableSet_cube]
  exact integrableOn_const (isCompact_cube.measure_lt_top.ne)
end Formalism.FourierDecayAlt.P.HLsc
