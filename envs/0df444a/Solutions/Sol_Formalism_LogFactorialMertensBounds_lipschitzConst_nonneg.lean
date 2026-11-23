-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.lipschitzConst_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:41:26.175145+00:00
-- url     : https://prove2.me/submissions/6ed1057c-1759-4428-9763-78fe56835d70

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open Formalism.LogFactorialMertensBounds
namespace Formalism.LogFactorialMertensBounds
theorem _root_.solution : 0 ≤ K0 := by
  unfold K0
  have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  linarith
end Formalism.LogFactorialMertensBounds
