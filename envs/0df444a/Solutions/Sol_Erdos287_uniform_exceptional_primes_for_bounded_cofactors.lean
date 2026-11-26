-- Prove2me | solution 1 for Erdos287.uniform_exceptional_primes_for_bounded_cofactors
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:00:31.107868+00:00
-- url     : https://prove2.me/submissions/5b428655-93dc-4a81-a8d8-11a0463e750a

import Mathlib
import Theorems.Thm_Erdos287_cofactor_subsum_count_from_prime_factorization_of_lcm
import Theorems.Thm_Erdos287_few_exceptional_primes_for_cofactor_subsets
import Theorems.Thm_Erdos287_prime_power_cofactor_certificate

open Finset

set_option autoImplicit false

/-- A single exceptional-prime set works for all denominator sequences and
all prime-power exponents with the given cofactor bound. -/
theorem solution (B Z Y H K : ℕ) (hY : 2 ≤ Y) (hBY : B < Y)
    (hbound : B * ((Finset.Icc 1 B).lcm id) < Y ^ (K + 1)) :
    let L := (Finset.Icc 1 B).lcm id
    ∃ E : Finset ℕ, E ⊆ Finset.Icc Y H ∧ (∀ p ∈ E, p.Prime) ∧
      E.card ≤ ((B + 1) * ∏ p ∈ L.primeFactors,
        if p ≤ Z then p ^ L.factorization p else 2 ^ (B / p)) * K ∧
      ∀ (k : ℕ) (f : ℕ → ℕ), 2 ≤ k →
        (∀ i < k, 1 < f i) → (∀ i j, i < j → j < k → f i < f j) →
        (∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) → f (k - 1) ≤ H →
        ∀ p e : ℕ, p.Prime → Y ≤ p → 1 ≤ e → p ∉ E →
          f (k - 1) < (B + 1) * p ^ e → ∀ i < k, ¬ p ^ e ∣ f i := by
  classical
  dsimp only
  let U := Icc 1 B
  let L := U.lcm id
  obtain ⟨F, hF, hrepr, hFbound⟩ :=
    Erdos287.cofactor_subsum_count_from_prime_factorization_of_lcm B Z
  let num (T : Finset ℕ) := ∑ c ∈ T, L / c
  let E := (Icc Y H).filter (fun p => p.Prime ∧ ∃ T ∈ F, p ∣ num T)
  have hU (c : ℕ) (hc : c ∈ U) : 0 < c ∧ c ∣ L :=
    ⟨(mem_Icc.mp hc).1, dvd_lcm hc⟩
  have hL : 0 < L := by
    apply Nat.pos_of_ne_zero
    apply Finset.lcm_ne_zero_iff.mpr
    intro c hc
    exact (hU c hc).1.ne'
  have hcount : E.card ≤ F.card * K := by
    refine Erdos287.few_exceptional_primes_for_cofactor_subsets U E F L Y K hL hY hU hF
      (fun p hp => ⟨(mem_filter.mp hp).2.1, (mem_Icc.mp (mem_filter.mp hp).1).1⟩)
      (by simpa [U, L] using hbound) (fun p hp => (mem_filter.mp hp).2.2)
  refine ⟨E, filter_subset _ _, (fun p hp => (mem_filter.mp hp).2.1),
    hcount.trans (Nat.mul_le_mul_right _ hFbound), ?_⟩
  intro k f hk hf1 hmono hsum hH p e hp hpY he hpE hmax
  have hfM (i : ℕ) (hi : i < k) : f i ≤ f (k - 1) := by
    rcases eq_or_lt_of_le (show i ≤ k - 1 by omega) with rfl | hlt
    · rfl
    · exact (hmono i (k - 1) hlt (by omega)).le
  by_cases hpH : p ≤ H
  · apply Erdos287.prime_power_cofactor_certificate k hk f hf1 hmono hsum p e hp he U
    · intro c hc
      have ⟨hpos, hle⟩ := mem_Icc.mp hc
      exact ⟨hpos, fun h => (hle.trans_lt (hBY.trans_le hpY)).not_ge (Nat.le_of_dvd hpos h)⟩
    · intro i hi hd
      have hpos : 0 < f i := (hf1 i hi).pos
      have hfac := Nat.div_mul_cancel hd
      have hlt : (f i / p ^ e) * p ^ e < (B + 1) * p ^ e := hfac.symm ▸ (hfM i hi).trans_lt hmax
      exact mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd hpos hd) (pow_pos hp.pos _),
        Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hlt)⟩
    · intro T hTU hTN hdiv
      obtain ⟨V, hV, hsame⟩ := hrepr T hTU hTN
      have hdivV : p ∣ num V := by
        change p ∣ ∑ x ∈ V, (Icc 1 B).lcm id / x
        rw [hsame]
        exact hdiv
      exact hpE (mem_filter.mpr ⟨mem_Icc.mpr ⟨hpY, hpH⟩, hp, V, hV, hdivV⟩)
  · intro i hi hd
    have hd' := (pow_dvd_pow p he).trans hd
    have hpM := Nat.le_of_dvd (hf1 i hi).pos (by simpa only [pow_one] using hd')
    exact hpH (hpM.trans ((hfM i hi).trans hH))

