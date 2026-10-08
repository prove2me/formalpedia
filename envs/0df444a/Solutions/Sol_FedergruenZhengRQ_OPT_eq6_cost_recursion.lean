-- Prove2me | solution 1 for FedergruenZhengRQ.OPT.eq6_cost_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:44:12.588636+00:00
-- url     : https://prove2.me/submissions/e7f37016-5bb9-468a-a534-30062bc144d7

import Mathlib
import Definitions.Def_FedergruenZhengRQ_OPT_Model

open FedergruenZhengRQ.OPT in
theorem solution (κ : ℝ) (G : ℤ → ℝ) (y₁ : ℤ) (Q : ℕ) (hQ : 1 ≤ Q) :
    Cstar κ G y₁ (Q + 1) = ((Q : ℝ) * Cstar κ G y₁ Q + G (y G y₁ (Q + 1))) / ((Q : ℝ) + 1) ∧
    (Cstar κ G y₁ (Q + 1) < Cstar κ G y₁ Q ↔ G (y G y₁ (Q + 1)) < Cstar κ G y₁ Q) := by
  have hQ0 : (Q : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    linarith
  have hQ1 : (0 : ℝ) < (Q : ℝ) + 1 := by positivity
  have hrec : Cstar κ G y₁ (Q + 1) =
      ((Q : ℝ) * Cstar κ G y₁ Q + G (y G y₁ (Q + 1))) / ((Q : ℝ) + 1) := by
    unfold Cstar
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ Q + 1)]
    push_cast
    rw [mul_div_cancel₀ _ hQ0]
    ring
  refine ⟨hrec, ?_⟩
  rw [hrec, div_lt_iff₀ hQ1]
  constructor <;> intro h <;> nlinarith
