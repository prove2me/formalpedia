-- Prove2me | solution 1 for Formalism.IncomingBounds.num_fact_add_q
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:17.629621+00:00
-- url     : https://prove2.me/submissions/88d07a96-6523-423d-be25-96ebecdd3b6d

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
theorem _root_.solution (a k : ℕ) :
    (((a + k).factorial : ℕ) : ℚ) = (a.factorial : ℚ) * ∏ j ∈ Finset.range k, ((a : ℚ) + j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, Nat.cast_mul, ih, Finset.prod_range_succ]
    push_cast
    ring
end Formalism.IncomingBounds
