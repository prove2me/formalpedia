-- Prove2me | solution 1 for BFFPyramidal.two_le_multiplicity_bound_arith
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-13T18:51:44.127515+00:00
-- url     : https://prove2.me/submissions/cb9d91e4-5350-44b5-b4dc-13ef9d7a1b72

import Mathlib
import Definitions.Def_BFFPyramidal_arithmetic

open BFFPyramidal

/-- For `2 ≤ n`, the greatest prime factor of `n` is indeed a prime factor of `n`. -/
private lemma maxPrimeFac_mem_primeFactors {n : ℕ} (hn : 2 ≤ n) :
    maxPrimeFac n ∈ n.primeFactors := by
  have hne : n.primeFactors.Nonempty := by
    refine ⟨n.minFac, ?_⟩
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd n, by omega⟩
  obtain ⟨i, hi, hsup⟩ := Finset.exists_mem_eq_sup n.primeFactors hne id
  show n.primeFactors.sup id ∈ n.primeFactors
  rw [hsup]
  exact hi

/-- The main arithmetic inequality: `n ≤ P(n) * φ(n)` for `n ≥ 2`. -/
private lemma le_maxPrimeFac_mul_totient : ∀ n : ℕ, 2 ≤ n → n ≤ maxPrimeFac n * n.totient := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hn0 : n ≠ 0 := by omega
    set p := maxPrimeFac n with hp_def
    have hpmem := maxPrimeFac_mem_primeFactors hn
    rw [Nat.mem_primeFactors] at hpmem
    obtain ⟨hp, hpdvd, -⟩ := hpmem
    set a := n.factorization p with ha_def
    have ha : 0 < a := hp.factorization_pos_of_dvd hn0 hpdvd
    set m := n / p ^ a with hm_def
    have hsplit : p ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hm0 : 0 < m := Nat.ordCompl_pos p hn0
    have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn0
    have hcop : Nat.Coprime (p ^ a) m := (Nat.coprime_ordCompl hp hn0).pow_left _
    have hpa : p * p ^ (a - 1) = p ^ a := by
      rw [← pow_succ']
      congr 1
      omega
    have htot : n.totient = p ^ (a - 1) * (p - 1) * m.totient := by
      rw [← hsplit, Nat.totient_mul hcop, Nat.totient_prime_pow hp ha]
    -- the heart of the matter : `m ≤ (p - 1) * φ m`
    have hkey : m ≤ (p - 1) * m.totient := by
      rcases Nat.lt_or_ge m 2 with h1 | h1
      · -- `m = 1`
        have hm1 : m = 1 := by omega
        rw [hm1, Nat.totient_one, mul_one]
        have := hp.two_le
        omega
      · -- `2 ≤ m`, use the induction hypothesis
        have hm2 : 2 ≤ m := h1
        have hmn : m < n := by
          have h2 : 2 ≤ p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
          have := Nat.mul_le_mul_right m h2
          rw [hsplit] at this
          omega
        have hmdvd : m ∣ n := ⟨p ^ a, by rw [← hsplit]; ring⟩
        have hqmem := maxPrimeFac_mem_primeFactors hm2
        have hqn : maxPrimeFac m ∈ n.primeFactors := Nat.primeFactors_mono hmdvd hn0 hqmem
        have hqdvd : maxPrimeFac m ∣ m := Nat.dvd_of_mem_primeFactors hqmem
        have hqle : maxPrimeFac m ≤ p := by
          rw [hp_def, maxPrimeFac]
          exact Finset.le_sup (f := id) hqn
        have hqne : maxPrimeFac m ≠ p := by
          intro h
          exact hpm (h ▸ hqdvd)
        calc m ≤ maxPrimeFac m * m.totient := ih m hmn hm2
          _ ≤ (p - 1) * m.totient := Nat.mul_le_mul_right _ (by omega)
    calc n = p ^ a * m := hsplit.symm
      _ ≤ p ^ a * ((p - 1) * m.totient) := Nat.mul_le_mul_left _ hkey
      _ = p * (p ^ (a - 1) * (p - 1) * m.totient) := by rw [← hpa]; ring
      _ = p * n.totient := by rw [htot]

theorem solution (l : ℕ) (hl : 2 ≤ l) :
    2 ≤ (maxPrimeFac l * Nat.totient l) / l + 1 := by
  have h := le_maxPrimeFac_mul_totient l hl
  have h2 : 0 < (maxPrimeFac l * Nat.totient l) / l := Nat.div_pos h (by omega)
  omega
