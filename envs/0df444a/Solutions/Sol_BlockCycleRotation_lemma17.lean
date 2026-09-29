-- Prove2me | solution 1 for BlockCycleRotation.lemma17
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:30:40.534844+00:00
-- url     : https://prove2.me/submissions/368bcf0d-5210-4e26-9b39-618181c8431c

import Definitions.Def_BlockCycleRotation_Constant
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_sum_div_sq_eq
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
/-- **Lemma 17.**

`G₁(n) = C·n²·∑_{d∣n} 1/d²` up to the sum of the per-divisor errors.  Each of
those is bounded by `lemma17_local`, and by `error_per_divisor_le` and
`sum_divisors_le` they total `O(n^{3/2+ε})`. -/
theorem solution {n : ℕ} (hn : 0 < n) (E : ℕ → ℝ)
    (hE : ∀ d ∈ n.divisors,
      |(∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
            ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
              + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
          - ((n / d : ℕ) : ℝ) ^ 2 * cConst| ≤ E d) :
    |G1 n - cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2|
      ≤ ∑ d ∈ n.divisors, E d:= by
  have hmain : cConst * (n : ℝ) ^ 2 * ∑ d ∈ n.divisors, 1 / (d : ℝ) ^ 2
      = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ^ 2 * cConst := by
    rw [← sum_div_sq_eq hn cConst]
    exact Finset.sum_congr rfl fun d _ => mul_comm _ _
  rw [G1, hmain, ← Finset.sum_sub_distrib]
  calc |∑ d ∈ n.divisors,
        ((∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
            ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
              + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
          - ((n / d : ℕ) : ℝ) ^ 2 * cConst)|
      ≤ ∑ d ∈ n.divisors,
          |(∑ p ∈ (coprimePairs (n / d)).filter (fun p => d * p.1 * (p.1 + p.2) ≤ n / d),
              ((d : ℝ) * ((n / d : ℕ) : ℝ) / ((p.1 : ℝ) + (p.2 : ℝ))
                + ((n / d : ℕ) : ℝ) ^ 2 * cTerm p))
            - ((n / d : ℕ) : ℝ) ^ 2 * cConst| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ n.divisors, E d := Finset.sum_le_sum hE
