-- Prove2me | solution 1 for Erdos287.no_denominator_multiple_of_large_prime_above_third
-- status  : ACCEPTED   (prove)
-- author  : @0xbf
-- created : 2026-11-11T19:34:52.231208+00:00
-- url     : https://prove2.me/submissions/a981f92e-e217-4e8f-83bf-469649c9d2fb

import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Tactic

open Finset

/-- The `p`-adic norm of the reciprocal of a nonzero natural number. -/
private lemma padicNorm_one_div_gen (p : ℕ) [Fact p.Prime] (m : ℕ) (hm : m ≠ 0) :
    padicNorm p ((1 : ℚ) / (m : ℚ)) = (p : ℚ) ^ (padicValNat p m : ℤ) := by
  have hm' : ((m : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [one_div, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hm'), padicValRat.inv,
    padicValRat.of_nat]
  norm_num

/-- **Multiplicity of the maximal valuation.**  For every prime `p` and every index `i` there is
a different index whose denominator is at least as divisible by `p`. -/
theorem padic_multiplicity (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (p : ℕ) (hp : Nat.Prime p) (i : ℕ) (hi : i < k) :
    ∃ j, j < k ∧ j ≠ i ∧ padicValNat p (f i) ≤ padicValNat p (f j) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨j₀, hj₀k, hj₀ne⟩ : ∃ j, j < k ∧ j ≠ i := by
    rcases Nat.eq_zero_or_pos i with h | h
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, by omega⟩
  by_contra hcon
  push_neg at hcon
  set a := padicValNat p (f i) with ha
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp.one_lt
  have hpos : (0 : ℚ) < (p : ℚ) ^ (a : ℤ) := by
    have h0 : (0 : ℚ) < (p : ℚ) := by linarith
    positivity
  have hterm : padicNorm p ((1 : ℚ) / (f i : ℚ)) = (p : ℚ) ^ (a : ℤ) :=
    padicNorm_one_div_gen p (f i) (by have := hf1 i hi; omega)
  have hrest : padicNorm p (∑ j ∈ (Finset.range k).erase i, (1 : ℚ) / (f j : ℚ))
      < (p : ℚ) ^ (a : ℤ) := by
    refine padicNorm.sum_lt' (fun j hj => ?_) hpos
    have hjk : j < k := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    have hjne : j ≠ i := Finset.ne_of_mem_erase hj
    rw [padicNorm_one_div_gen p (f j) (by have := hf1 j hjk; omega)]
    exact zpow_lt_zpow_right₀ hp1 (by exact_mod_cast hcon j hjk hjne)
  have hsplit : padicNorm p (1 : ℚ) = (p : ℚ) ^ (a : ℤ) := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hi),
      padicNorm.add_eq_max_of_ne (by rw [hterm]; exact fun h => absurd h.symm (ne_of_lt hrest)),
      hterm, max_eq_left (le_of_lt hrest)]
  rw [padicNorm.one] at hsplit
  have ha0 : a = 0 := by
    by_contra h
    have h1 : (1 : ℚ) < (p : ℚ) ^ (a : ℤ) := by
      calc (1 : ℚ) = (p : ℚ) ^ (0 : ℤ) := by norm_num
        _ < (p : ℚ) ^ (a : ℤ) := by
            refine zpow_lt_zpow_right₀ hp1 ?_
            exact_mod_cast Nat.pos_of_ne_zero h
    rw [← hsplit] at h1
    exact absurd h1 (by norm_num)
  have := hcon j₀ hj₀k hj₀ne
  omega

private lemma padicNorm_three_div_two_mul (p : ℕ) [Fact p.Prime] (hp : 3 < p) :
    padicNorm p ((3 : ℚ) / (2 * p)) = (p : ℚ) := by
  have hp2 : ¬ p ∣ 2 := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < 2) h
    omega
  have hp3 : ¬ p ∣ 3 := by
    intro h
    have hle := Nat.le_of_dvd (by omega : 0 < 3) h
    omega
  have hval2 : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd hp2
  have hval3 : padicValNat p 3 = 0 := padicValNat.eq_zero_of_not_dvd hp3
  have hvaldenN : padicValNat p (2 * p) = 1 := by
    rw [padicValNat.mul (by omega) (by exact (Fact.out : Nat.Prime p).ne_zero), hval2,
      padicValNat_self]
  have hvaltop : padicValRat p ((3 : ℕ) : ℚ) = 0 := by
    rw [padicValRat.of_nat, hval3]
    norm_num
  have hvalden : padicValRat p (((2 * p : ℕ) : ℚ)) = 1 := by
    rw [padicValRat.of_nat, hvaldenN]
    norm_num
  have hrat : (3 : ℚ) / (2 * p) = ((3 : ℕ) : ℚ) / ((2 * p : ℕ) : ℚ) := by
    push_cast
    ring
  have hval : padicValRat p ((3 : ℚ) / (2 * p)) = -1 := by
    rw [hrat, padicValRat.div (by norm_num) (by positivity), hvaltop, hvalden]
    norm_num
  rw [padicNorm.eq_zpow_of_nonzero (by positivity), hval]
  norm_num

private lemma dvd_lt_three_cases {p x N : ℕ} (hp : 0 < p) (hN : N < 3 * p)
    (hx : x ≤ N) (hxpos : 0 < x) (hd : p ∣ x) : x = p ∨ x = 2 * p := by
  rcases hd with ⟨q, hq⟩
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := by omega
    rw [hq0] at hq
    omega
  have hq_lt : q < 3 := by
    by_contra h
    have hq3 : 3 ≤ q := by omega
    have hpq : 3 * p ≤ p * q := by
      calc
        3 * p = p * 3 := by omega
        _ ≤ p * q := Nat.mul_le_mul_left p hq3
    rw [hq] at hx
    omega
  rcases (by omega : q = 1 ∨ q = 2) with hq1 | hq2
  · left
    rw [hq, hq1]
    omega
  · right
    rw [hq, hq2]
    omega

theorem solution
    (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hdist : ∀ i j, i < k → j < k → i ≠ j → f i ≠ f j)
    (N : ℕ) (hbound : ∀ i, i < k → f i ≤ N)
    (p : ℕ) (hp : Nat.Prime p) (hp3 : 3 < p) (hN : N < 3 * p)
    (i : ℕ) (hi : i < k) : ¬ p ∣ f i := by
  intro hdivi
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j, hj, hjne, hval⟩ := padic_multiplicity k hk f hf1 hsum p hp i hi
  have hvi : 1 ≤ padicValNat p (f i) := by
    apply (padicValNat_dvd_iff_le (by have := hf1 i hi; omega : f i ≠ 0)).mp
    simpa using hdivi
  have hvj : 1 ≤ padicValNat p (f j) := le_trans hvi hval
  have hdivj : p ∣ f j := by
    have hpow : p ^ 1 ∣ f j :=
      (padicValNat_dvd_iff_le (by have := hf1 j hj; omega : f j ≠ 0)).mpr hvj
    simpa using hpow
  have hfi_cases : f i = p ∨ f i = 2 * p :=
    dvd_lt_three_cases (by omega) hN (hbound i hi) (by have := hf1 i hi; omega) hdivi
  have hfj_cases : f j = p ∨ f j = 2 * p :=
    dvd_lt_three_cases (by omega) hN (hbound j hj) (by have := hf1 j hj; omega) hdivj
  have hpaircases : (f i = p ∧ f j = 2 * p) ∨ (f i = 2 * p ∧ f j = p) := by
    rcases hfi_cases with hfi | hfi <;> rcases hfj_cases with hfj | hfj
    · exfalso
      exact hdist i j hi hj (Ne.symm hjne) (by rw [hfi, hfj])
    · exact Or.inl ⟨hfi, hfj⟩
    · exact Or.inr ⟨hfi, hfj⟩
    · exfalso
      exact hdist i j hi hj (Ne.symm hjne) (by rw [hfi, hfj])
  have hno_other : ∀ l, l < k → l ≠ i → l ≠ j → ¬ p ∣ f l := by
    intro l hl hli hlj hdivl
    have hfl_cases : f l = p ∨ f l = 2 * p :=
      dvd_lt_three_cases (by omega) hN (hbound l hl) (by have := hf1 l hl; omega) hdivl
    rcases hpaircases with ⟨hfi, hfj⟩ | ⟨hfi, hfj⟩
    · rcases hfl_cases with hfl | hfl
      · exact hdist l i hl hi hli (by rw [hfl, hfi])
      · exact hdist l j hl hj hlj (by rw [hfl, hfj])
    · rcases hfl_cases with hfl | hfl
      · exact hdist l j hl hj hlj (by rw [hfl, hfj])
      · exact hdist l i hl hi hli (by rw [hfl, hfi])
  let U : ℕ → ℚ := fun l => (1 : ℚ) / f l
  let T : Finset ℕ := Finset.range k
  let R : Finset ℕ := (T.erase i).erase j
  have hmemi : i ∈ T := Finset.mem_range.mpr hi
  have hmemj : j ∈ T.erase i := Finset.mem_erase.mpr ⟨hjne, Finset.mem_range.mpr hj⟩
  have hsplit : (∑ l ∈ T, U l) = U i + U j + ∑ l ∈ R, U l := by
    calc
      (∑ l ∈ T, U l) = U i + ∑ l ∈ T.erase i, U l := by
        rw [← Finset.add_sum_erase _ _ hmemi]
      _ = U i + (U j + ∑ l ∈ R, U l) := by
        rw [← Finset.add_sum_erase _ _ hmemj]
      _ = U i + U j + ∑ l ∈ R, U l := by ring
  have hpairval : U i + U j = (3 : ℚ) / (2 * p) := by
    rcases hpaircases with ⟨hfi, hfj⟩ | ⟨hfi, hfj⟩
    · simp only [U, hfi, hfj]
      push_cast
      field_simp
      <;> ring
    · simp only [U, hfi, hfj]
      push_cast
      field_simp
      <;> ring
  have hrestbound : padicNorm p (∑ l ∈ R, U l) ≤ 1 := by
    apply padicNorm.sum_le'
    · intro l hl
      rcases Finset.mem_erase.mp hl with ⟨hlj, hli_mem⟩
      rcases Finset.mem_erase.mp hli_mem with ⟨hli, hlT⟩
      have hlk : l < k := Finset.mem_range.mp hlT
      have hnotdiv : ¬ p ∣ f l := hno_other l hlk hli hlj
      have hvl : padicValNat p (f l) = 0 := padicValNat.eq_zero_of_not_dvd hnotdiv
      change padicNorm p ((1 : ℚ) / (f l : ℚ)) ≤ 1
      rw [padicNorm_one_div_gen p (f l) (by have := hf1 l hlk; omega), hvl]
      norm_num
    · norm_num
  have hpairnorm : padicNorm p (U i + U j) = (p : ℚ) := by
    rw [hpairval]
    exact padicNorm_three_div_two_mul p hp3
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast (by omega : 1 < p)
  have hrestlt : padicNorm p (∑ l ∈ R, U l) < (p : ℚ) := lt_of_le_of_lt hrestbound hp1
  have hnormne : padicNorm p (U i + U j) ≠ padicNorm p (∑ l ∈ R, U l) := by
    rw [hpairnorm]
    exact ne_of_gt hrestlt
  have hsum_norm : padicNorm p (∑ l ∈ T, U l) = 1 := by
    rw [hsum]
    exact padicNorm.one
  have hsum_norm_p : padicNorm p (∑ l ∈ T, U l) = (p : ℚ) := by
    rw [hsplit, padicNorm.add_eq_max_of_ne hnormne, hpairnorm, max_eq_left (le_of_lt hrestlt)]
  rw [hsum_norm] at hsum_norm_p
  exact (ne_of_lt hp1) hsum_norm_p
