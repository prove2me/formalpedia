-- Prove2me | solution 1 for BlockCycleRotation.Q_eq_tripleSum_decomposed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:12:38.163772+00:00
-- url     : https://prove2.me/submissions/a8e8c77c-a478-4b51-ba34-100cc4ea9e44

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_Q_eq_tripleSum
import Theorems.Thm_BlockCycleRotation_coprimeTriples_decompose
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **The triple sum in estimable form.**

`Q(n)` as a sum over divisors `d ∣ n`, coprime pairs `(a, a')`, and `b'` in an
initial segment filtered by the divisibility condition.  By `inner_sum_nat_eq`
the innermost sum is an arithmetic-progression sum of a linear function, which
`inner_sum_sub_main_le` estimates. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ p ∈ coprimePairs (n / d),
          ∑ b' ∈ (Finset.Ico 1 (bBound (n / d) p.1 p.2)).filter
            (fun b' => p.1 ∣ (n / d - p.2 * b')), (n / d - p.2 * b') / p.1:= by
  rw [Q_eq_tripleSum hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have hm : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  exact coprimeTriples_decompose hm (fun a a' b' => (n / d - a' * b') / a)
