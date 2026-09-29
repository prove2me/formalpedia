-- Prove2me | solution 1 for BlockCycleRotation.heilbron
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:06:18.276164+00:00
-- url     : https://prove2.me/submissions/6f8b2239-eb30-48bf-b2a2-b9ee41f19c04

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_cf_spec
import Theorems.Thm_BlockCycleRotation_remSum_eq_sum_K
import Theorems.Thm_BlockCycleRotation_sum_split_eq_sum_quadruples
import Theorems.Thm_BlockCycleRotation_sum_fst_eq_sum_snd
import Theorems.Thm_BlockCycleRotation_sum_allShifts_eq
import Theorems.Thm_BlockCycleRotation_sum_remSum_allShifts
import Theorems.Thm_BlockCycleRotation_sum_snd_quadruplesAll
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

theorem mem_shifts {n k : ℕ} :
    k ∈ shifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.gcd n k = 1 := by
  simp [shifts]

/-- **The left-hand side of (eq. heilbron).**  Summing `remSum` over the shifts
splits into a count of shifts plus a double sum of continuants over splits. -/
theorem sum_remSum_eq (n : ℕ) :
    ∑ k ∈ shifts n, remSum n k
      = (shifts n).card
        + ∑ k ∈ shifts n, ∑ j ∈ Finset.Ico 1 (cf n k).length, K ((cf n k).take j) := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  obtain ⟨-, hk1, hk2, hgcd⟩ := mem_shifts.1 hk
  have hkn : k < n := by omega
  have hne : cf n k ≠ [] := (cf_spec k n hk1 hkn hgcd).1
  have hlen : 0 < (cf n k).length := List.length_pos_iff.2 hne
  rw [remSum_eq_sum_K k n hk1 hkn hgcd, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot hlen]
  simp

/-- **The coprime form of the Heilbronn identity.**

Summing the Euclidean remainder sums over the shifts the block cycle algorithm
recurses on *that are coprime to `n`* equals the number of those shifts plus a
sum over Heilbronn's quadruples.  The first term is the paper's `∑ gcd(n,k)`,
which is a count here because the shifts are coprime to `n`.

This is the unlabelled display preceding equation (eq. heilbron) in the paper.
Equation (eq. heilbron) itself drops both coprimality restrictions, and follows
from this by summing over `d = gcd(n,k)`; see `remSum_mul` for the scaling that
aggregation relies on. -/
theorem heilbron_coprime (n : ℕ) :
    ∑ k ∈ shifts n, remSum n k = (shifts n).card + ∑ q ∈ quadruples n, q.1 := by
  rw [sum_remSum_eq, sum_split_eq_sum_quadruples]

/-- The gcds, aggregated over the gcd. -/
theorem sum_gcd_allShifts {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, Nat.gcd n k = ∑ g ∈ n.divisors, g * (shifts (n / g)).card := by
  rw [sum_allShifts_eq hn (fun g _ => g)]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Equation (eq. heilbron), aggregated form.**

Summing the Euclidean remainder sums over *all* shifts the algorithm recurses
on — not only those coprime to `n` — equals the sum of `gcd(n,k)` over the same
range plus a divisor-weighted sum over Heilbronn's quadruples.

This is the coprime form summed over `g = gcd(n,k)`.  The paper writes the
second term as a single sum over quadruples constrained only by
`gcd(a,a') = 1`; that regrouping is `sum_quadruplesAll` below. -/
theorem heilbron_aggregated {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k
      = (∑ k ∈ allShifts n, Nat.gcd n k)
        + ∑ g ∈ n.divisors, g * ∑ q ∈ quadruples (n / g), q.1 := by
  rw [sum_remSum_allShifts hn, sum_gcd_allShifts hn, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [heilbron_coprime (n / g), Nat.mul_add]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Equation (eq. heilbron).**

Summing the Euclidean remainder sums over all shifts the block cycle algorithm
recurses on equals the sum of `gcd(n,k)` over the same range, plus the sum of
`b` over the quadruples constrained only by `gcd(a,a') = 1`.

This is the paper's labelled identity, the passage from move counts to lattice
point counts. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ k ∈ allShifts n, remSum n k
      = (∑ k ∈ allShifts n, Nat.gcd n k) + ∑ q ∈ quadruplesAll n, q.2.1:= by
  rw [heilbron_aggregated hn, sum_snd_quadruplesAll hn]
  congr 1
  exact Finset.sum_congr rfl fun e _ => by rw [sum_fst_eq_sum_snd]
