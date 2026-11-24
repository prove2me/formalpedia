-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.Sz_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:46.783051+00:00
-- url     : https://prove2.me/submissions/f6621579-39e8-4589-bb86-984d80506a85

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Theorems.Thm_Formalism_LogFactorialMertensBounds_Icc_one_eq_Ioc

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
theorem _root_.solution (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx2 : x ≤ k + 1) :
    Sz x = x * A k - ∑ n ∈ Finset.Ioc 0 k, Λ n := by
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg k) hx1
  have key : ∀ k' : ℕ, ∑ n ∈ Finset.Icc 1 k', Λ n * (x / n - 1) =
      x * A k' - ∑ n ∈ Finset.Ioc 0 k', Λ n := by
    intro k'
    rw [Icc_one_eq_Ioc, A, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  unfold Sz
  rcases lt_or_eq_of_le hx2 with h | h
  · rw [show ⌊x⌋₊ = k from (Nat.floor_eq_iff hx0).2 ⟨hx1, h⟩, key]
  · subst h
    have hf : ⌊(k:ℝ) + 1⌋₊ = k + 1 := by
      rw [← Nat.cast_add_one, Nat.floor_natCast]
    have hone : ((k:ℝ) + 1) / (((k + 1 : ℕ)) : ℝ) = 1 := by
      push_cast
      exact div_self (by positivity)
    rw [hf, Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), key, hone]
    ring
end Formalism.LogFactorialMertensBounds
