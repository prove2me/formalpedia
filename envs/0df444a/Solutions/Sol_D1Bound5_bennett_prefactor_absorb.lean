-- Prove2me | solution 1 for D1Bound5.bennett_prefactor_absorb
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:10.511006+00:00
-- url     : https://prove2.me/submissions/6732fe67-0ce1-4fe7-880c-0a0afb520999

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5









/-- A prefactor at least one can be absorbed into an exponential at every
positive order, allowing the preceding exact rational slack to be used. -/
theorem _root_.solution (M H : ℝ) (hM : 1 ≤ M) (hH : 0 ≤ H)
    (k : ℕ) (hk : 1 ≤ k) : M * H ^ k ≤ (M * H) ^ k := by
  have hM0 : 0 ≤ M := by linarith
  have hpow : ∀ n : ℕ, 1 ≤ M ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      exact le_trans (by simpa using hM) (mul_le_mul_of_nonneg_right ih hM0)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hself : M ≤ M ^ (n + 1) := by
    rw [pow_succ]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hpow n) hM0
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hself (pow_nonneg hH _)

end D1Bound5
end
