-- Prove2me | solution 1 for Formalism.IncomingBounds.num_one_add_four_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:16.39142+00:00
-- url     : https://prove2.me/submissions/ea063a58-c515-485f-bd9a-0d8cec47142f

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
theorem _root_.solution (v : ℕ) : 1 + 4 * v ≤ 5 ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    have := Nat.one_le_pow v 5 (by norm_num)
    omega
end Formalism.IncomingBounds
