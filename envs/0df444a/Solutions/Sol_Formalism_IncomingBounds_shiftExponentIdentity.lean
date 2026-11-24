-- Prove2me | solution 1 for Formalism.IncomingBounds.shiftExponentIdentity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:43:20.471394+00:00
-- url     : https://prove2.me/submissions/c9f684f1-b9cd-43fb-978a-8246bb8a90b1

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
theorem _root_.solution : LemmaMExponent := by
  intro l hl s0
  have hl' : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hne : (l : ℝ) ^ 2 ≠ 1 := by nlinarith
  have hne' : (l : ℝ) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 hne
  refine ⟨?_, ?_⟩
  · rw [geom_sum_eq hne, rho, ← pow_mul, pow_succ]
    field_simp
    ring
  · intro s
    rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by ring
end Formalism.IncomingBounds
