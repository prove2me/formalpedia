-- Prove2me | solution 1 for Formalism.IncomingBounds.thmPExp_choose_div_factorial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:34:25.242799+00:00
-- url     : https://prove2.me/submissions/8b3c22a1-0bde-401e-9003-c7e6f91c1d97

import Definitions.Def_Formalism_IncomingBounds_DefsThmP
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ProdRangeEqFactorialMulProdIco
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_ThmPExp

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
open MvPowerSeries Finset
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution {K : Type} [Field K] [CharZero K] {k j : ℕ} (hjk : j ≤ k) :
    ((k.choose j : ℕ) : K) / (k.factorial : K) =
      1 / ((j.factorial : K) * ((k - j).factorial : K)) := by
  have h := congrArg (Nat.cast : ℕ → K) (Nat.choose_mul_factorial_mul_factorial hjk)
  push_cast at h
  have hk : (k.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hj : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hkj : ((k - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  rw [div_eq_div_iff hk (mul_ne_zero hj hkj), one_mul, ← h]
  ring
end Formalism.IncomingBounds
