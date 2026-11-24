-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas.four_le_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:05:58.299083+00:00
-- url     : https://prove2.me/submissions/0fbd90d7-d54d-4c3a-bc16-32543aec4eb0

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Nat
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
theorem _root_.solution (N : ℕ) (hN : 100 ≤ N) : 4 ≤ Real.log N := by
  have h1 : Real.exp 4 ≤ 100 := by
    have he := Real.exp_one_lt_d9
    have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h2]
    calc Real.exp 1 ^ 4 ≤ 2.7182818286 ^ 4 := pow_le_pow_left₀ (Real.exp_pos 1).le he.le 4
      _ ≤ 100 := by norm_num
  have h2 : (100 : ℝ) ≤ N := by exact_mod_cast hN
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.PrimeCountingLemmas
