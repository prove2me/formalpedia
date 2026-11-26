-- Prove2me | solution 1 for Erdos287.upper_valuation_residue
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T02:56:36.696726+00:00
-- url     : https://prove2.me/submissions/749a10ca-1ffb-41a2-bff9-2bdbf9246f36

import Mathlib

open Finset

set_option autoImplicit false

private theorem padicNorm_reciprocal {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0) :
    padicNorm p ((1 : ℚ) / m) = (p : ℚ) ^ (padicValNat p m : ℤ) := by
  have hm' : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [one_div, padicNorm.eq_zpow_of_nonzero (inv_ne_zero hm'), padicValRat.inv,
    padicValRat.of_nat, neg_neg]

private theorem padicNorm_prime_pow {p : ℕ} (hp : Nat.Prime p) (a : ℕ) :
    padicNorm p ((p : ℚ) ^ a) = (p : ℚ) ^ (-(a : ℤ)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  induction a with
  | zero => simp
  | succ a ih => rw [pow_succ, padicNorm.mul, ih, padicNorm.padicNorm_p hp.one_lt, pow_succ]

/-- Clearing the denominators across several upper valuation layers gives a prime-power congruence. -/
theorem solution (k : ℕ) (f : ℕ → ℕ) (hf : ∀ i, i < k → 0 < f i)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) (p b a L : ℕ)
    (hp : Nat.Prime p) (hb : 1 ≤ b) (hba : b ≤ a)
    (hmax : ∀ i, i < k → padicValNat p (f i) ≤ a)
    (hL : ∀ i, i < k → b ≤ padicValNat p (f i) → f i / p ^ padicValNat p (f i) ∣ L) :
    p ^ (a + 1 - b) ∣ ∑ i ∈ (Finset.range k).filter (fun i => b ≤ padicValNat p (f i)),
      (L / (f i / p ^ padicValNat p (f i))) * p ^ (a - padicValNat p (f i)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let v (i : ℕ) := padicValNat p (f i)
  let c (i : ℕ) := f i / p ^ v i
  let H := (range k).filter (fun i => b ≤ v i)
  let R := (range k).filter (fun i => ¬ b ≤ v i)
  let U : ℚ := ∑ i ∈ H, (1 : ℚ) / f i
  let W : ℚ := ∑ i ∈ R, (1 : ℚ) / f i
  let A : ℕ := ∑ i ∈ H, L / c i * p ^ (a - v i)
  change p ^ (a + 1 - b) ∣ A
  have hpq : (1 : ℚ) < p := by exact_mod_cast hp.one_lt
  have hppos : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hsplit : U + W = 1 := by
    exact (sum_filter_add_sum_filter_not (range k) (fun i => b ≤ v i) (fun i => (1 : ℚ) / f i)).trans hsum
  have hW : padicNorm p W ≤ (p : ℚ) ^ ((b - 1 : ℕ) : ℤ) := by
    apply padicNorm.sum_le' _ (zpow_nonneg hppos.le _)
    intro i hi
    obtain ⟨hir, hv⟩ := mem_filter.mp hi
    have hik := mem_range.mp hir
    have hv' : v i ≤ b - 1 := by omega
    rw [padicNorm_reciprocal (hf i hik).ne']
    exact zpow_le_zpow_right₀ hpq.le (by exact_mod_cast hv')
  have hU : padicNorm p U ≤ (p : ℚ) ^ ((b - 1 : ℕ) : ℤ) := by
    have hUW : U = 1 - W := eq_sub_of_add_eq hsplit
    rw [hUW]
    apply padicNorm.sub.trans
    rw [padicNorm.one]
    apply max_le _ hW
    rw [← zpow_zero (p : ℚ)]
    exact zpow_le_zpow_right₀ hpq.le (by positivity)
  have hrepr : (A : ℚ) = ((p : ℚ) ^ a * L) * U := by
    simp only [A, U, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, mul_sum]
    apply sum_congr rfl
    intro i hi
    obtain ⟨hir, hv⟩ := mem_filter.mp hi
    have hik := mem_range.mp hir
    have hvd : p ^ v i ∣ f i := (padicValNat_dvd_iff_le (hf i hik).ne').mpr le_rfl
    have hfc : (c i : ℚ) * (p : ℚ) ^ v i = f i := by
      exact_mod_cast Nat.div_mul_cancel hvd
    have hLc : ((L / c i : ℕ) : ℚ) * c i = L := by
      exact_mod_cast Nat.div_mul_cancel (hL i hik hv)
    rw [mul_one_div]
    apply (eq_div_iff (Nat.cast_ne_zero.mpr (hf i hik).ne')).mpr
    calc
      ((L / c i : ℕ) : ℚ) * (p : ℚ) ^ (a - v i) * f i =
          (((L / c i : ℕ) : ℚ) * c i) * ((p : ℚ) ^ (a - v i) * (p : ℚ) ^ v i) := by
        rw [← hfc]
        ac_rfl
      _ = (p : ℚ) ^ a * L := by
        rw [hLc, ← pow_add, Nat.sub_add_cancel (hmax i hik), mul_comm]
  rw [← Int.natCast_dvd_natCast, padicNorm.dvd_iff_norm_le, Int.cast_natCast, hrepr,
    padicNorm.mul, padicNorm.mul, padicNorm_prime_pow hp]
  calc
    (p : ℚ) ^ (-(a : ℤ)) * padicNorm p L * padicNorm p U
      ≤ (p : ℚ) ^ (-(a : ℤ)) * 1 * (p : ℚ) ^ ((b - 1 : ℕ) : ℤ) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (padicNorm.of_nat _) (by positivity)) hU
          (padicNorm.nonneg _) (by positivity)
    _ = (p : ℚ) ^ (-((a + 1 - b : ℕ) : ℤ)) := by
      rw [mul_one, ← zpow_add₀ hppos.ne']
      congr 1
      omega

