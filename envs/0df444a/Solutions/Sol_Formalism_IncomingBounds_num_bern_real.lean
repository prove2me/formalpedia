-- Prove2me | solution 1 for Formalism.IncomingBounds.num_bern_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:02:58.322528+00:00
-- url     : https://prove2.me/submissions/5fdad86c-3e0a-4d2f-9bc1-b4d48c8d2e87

import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution (a : ℝ) (ha : 1 ≤ a) (w : ℕ) : 1 + (w : ℝ) * (a - 1) ≤ a ^ w := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ a - 1 by linarith) w
  simpa using h
end Formalism.IncomingBounds
