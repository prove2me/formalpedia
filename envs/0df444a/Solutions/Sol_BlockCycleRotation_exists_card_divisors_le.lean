-- Prove2me | solution 1 for BlockCycleRotation.exists_card_divisors_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:42:36.839803+00:00
-- url     : https://prove2.me/submissions/6ea2a229-ed4d-47f7-ab11-6b39116354c3

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_exists_const_add_one_le_rpow
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

/-- `k + 1 ≤ 2 ^ k`. -/
theorem succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

/-- `(p^k)^ε = (p^ε)^k`. -/
theorem natPow_rpow {p : ℕ} (hp : 0 < p) (k : ℕ) (ε : ℝ) :
    (((p ^ k : ℕ) : ℝ)) ^ ε = (((p : ℝ)) ^ ε) ^ k := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  push_cast
  rw [← Real.rpow_natCast ((p : ℝ)) k, ← Real.rpow_mul hp0, mul_comm,
    Real.rpow_mul hp0, Real.rpow_natCast]

/-- **Large primes cost nothing.**  If `2 ≤ p^ε` then `k + 1 ≤ (p^k)^ε`. -/
theorem add_one_le_rpow_of_two_le {p : ℕ} (hp : 0 < p) {ε : ℝ} (h2 : 2 ≤ (p : ℝ) ^ ε)
    (k : ℕ) : ((k : ℝ) + 1) ≤ (((p ^ k : ℕ) : ℝ)) ^ ε := by
  rw [natPow_rpow hp k ε]
  have h1 : ((k : ℝ) + 1) ≤ 2 ^ k := by
    have := succ_le_two_pow k
    have hcast : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at hcast
    linarith
  exact h1.trans (pow_le_pow_left₀ (by norm_num) h2 k)

end BlockCycleRotation

open BlockCycleRotation in
/-- **The divisor bound.**  For every `ε > 0` there is a constant `C` with
`d(n) ≤ C · n^ε` for all `n ≥ 1`.

The primes dividing `n` are split at `p^ε = 2`.  Above the cut each factor
`k + 1 ≤ 2^k ≤ (p^ε)^k` costs nothing; below it — finitely many primes, all
less than `2^(1/ε)` — each costs a constant `C₀`, and their number is bounded
independently of `n`. -/
theorem solution {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → ((n.divisors.card : ℝ)) ≤ C * (n : ℝ) ^ ε:= by
  classical
  set N := ⌈(2 : ℝ) ^ (1 / ε)⌉₊ + 1 with hN
  set S := (Finset.range N).filter (fun p : ℕ => ¬ (2 ≤ (p : ℝ) ^ ε)) with hS
  obtain ⟨C₀, hC₀1, hC₀⟩ := exists_const_add_one_le_rpow hε
  have hC₀0 : (0 : ℝ) < C₀ := by linarith
  refine ⟨C₀ ^ S.card, by positivity, ?_⟩
  intro n hn
  -- every prime below the cut lies in `S`
  have hmemS : ∀ p : ℕ, 2 ≤ p → ¬ (2 ≤ (p : ℝ) ^ ε) → p ∈ S := by
    intro p hp2 hlt
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hlt' : (p : ℝ) ^ ε < 2 := lt_of_not_ge hlt
    have hinv : (0 : ℝ) < 1 / ε := by positivity
    have h1 : ((p : ℝ) ^ ε) ^ (1 / ε) = (p : ℝ) := by
      rw [← Real.rpow_mul hp0, mul_one_div, div_self hε.ne', Real.rpow_one]
    have h2 : ((p : ℝ) ^ ε) ^ (1 / ε) < (2 : ℝ) ^ (1 / ε) :=
      Real.rpow_lt_rpow (by positivity) hlt' hinv
    rw [h1] at h2
    have h3 : (p : ℝ) < (⌈(2 : ℝ) ^ (1 / ε)⌉₊ : ℝ) :=
      lt_of_lt_of_le h2 (Nat.le_ceil _)
    have h4 : p < N := by
      have : p < ⌈(2 : ℝ) ^ (1 / ε)⌉₊ := by exact_mod_cast h3
      omega
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨h4, hlt⟩
  rw [Nat.card_divisors hn]
  push_cast
  -- bound each factor
  have hfac : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ (if p ∈ S then C₀ else 1) * (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : 2 ≤ p := hpp.two_le
    by_cases hsm : 2 ≤ (p : ℝ) ^ ε
    · have hnot : p ∉ S := by simp [hS, hsm]
      rw [if_neg hnot, one_mul]
      exact add_one_le_rpow_of_two_le (by omega) hsm _
    · rw [if_pos (hmemS p hp2 hsm)]
      exact hC₀ p hp2 _
  -- the constant part
  have hconst : (∏ p ∈ n.primeFactors, (if p ∈ S then C₀ else 1)) ≤ C₀ ^ S.card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    refine pow_le_pow_right₀ hC₀1 ?_
    refine Finset.card_le_card ?_
    intro x hx
    exact (Finset.mem_filter.1 hx).2
  -- the `n^ε` part
  have hprod_n : (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ)) = (n : ℝ) := by
    rw [← Nat.cast_prod]
    exact congrArg _ (Nat.prod_primeFactors_pow_factorization hn).symm
  have hrpow : (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε)
      = (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (fun p _ => by positivity) ε, hprod_n]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors,
          ((if p ∈ S then C₀ else 1) * (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) :=
        Finset.prod_le_prod (fun p _ => by positivity) hfac
    _ = (∏ p ∈ n.primeFactors, (if p ∈ S then C₀ else 1))
          * (∏ p ∈ n.primeFactors, (((p ^ n.factorization p : ℕ)) : ℝ) ^ ε) :=
        Finset.prod_mul_distrib
    _ = (∏ p ∈ n.primeFactors, (if p ∈ S then C₀ else 1)) * (n : ℝ) ^ ε := by rw [hrpow]
    _ ≤ C₀ ^ S.card * (n : ℝ) ^ ε := by
        refine mul_le_mul_of_nonneg_right hconst ?_
        positivity
