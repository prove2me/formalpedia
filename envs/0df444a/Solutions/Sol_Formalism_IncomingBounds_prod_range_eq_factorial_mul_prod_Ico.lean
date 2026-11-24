-- Prove2me | solution 1 for Formalism.IncomingBounds.prod_range_eq_factorial_mul_prod_Ico
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:19.63294+00:00
-- url     : https://prove2.me/submissions/aa2bd434-7344-4fb6-8275-65768d43c198

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
theorem _root_.solution (m x : ℕ) :
    ∏ j ∈ Finset.range m, ((((m + 1) * x : ℕ) : ℚ) + j + 1) =
      (m.factorial : ℚ) * ∏ i ∈ Finset.Ico 1 (m + 1), (1 + ((m + 1 : ℕ) : ℚ) * (x : ℚ) / (i : ℚ)) := by
  rw [Finset.prod_Ico_eq_prod_range, show m + 1 - 1 = m by omega,
    ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
end Formalism.IncomingBounds
