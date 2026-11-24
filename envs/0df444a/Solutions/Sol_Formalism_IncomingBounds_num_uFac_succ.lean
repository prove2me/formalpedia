-- Prove2me | solution 1 for Formalism.IncomingBounds.num_uFac_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:48:52.031105+00:00
-- url     : https://prove2.me/submissions/34f33315-637c-433c-8e8f-7c95d3be6f5d

import Definitions.Def_Formalism_IncomingBounds_LemmaMNumerics
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Theorems.Thm_Formalism_IncomingBounds_num_fact_add_q
import Theorems.Thm_Formalism_IncomingBounds_prod_range_eq_factorial_mul_prod_Ico

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
    uFac (m + 1) (x + 1) = uFac (m + 1) x * (-(m.factorial : ℚ) *
      ∏ i ∈ Finset.Ico 1 (m + 1), (1 + ((m + 1 : ℕ) : ℚ) * (x : ℚ) / (i : ℚ))) := by
  unfold uFac
  rw [show (m + 1) * (x + 1) = (m + 1) * x + (m + 1) by ring, num_fact_add_q,
    Finset.prod_range_succ, prod_range_eq_factorial_mul_prod_Ico m x, Nat.factorial_succ x]
  have h1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  have h2 : ((x : ℚ) + 1) ≠ 0 := by positivity
  have h3 : ((x.factorial : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring
end Formalism.IncomingBounds
