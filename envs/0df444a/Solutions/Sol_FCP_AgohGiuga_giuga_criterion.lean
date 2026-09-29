-- Prove2me | solution 1 for FCP.AgohGiuga.giuga_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-15T21:19:06.354254+00:00
-- url     : https://prove2.me/submissions/b95f0769-546c-4819-be3f-78399962e90c

import Mathlib

open Finset


/-- The sum of `x ^ k` over a finite field, for `k ≥ 1`: it is `-1` when `q - 1 ∣ k`
and `0` otherwise. -/
private theorem giuga_sum_pow_field (K : Type) [Field K] [Fintype K] (k : ℕ) (hk : 0 < k) :
    ∑ x : K, x ^ k = if Fintype.card K - 1 ∣ k then -1 else 0 := by
  classical
  have h1 : ∑ x : K, x ^ k = ∑ x ∈ univ \ {(0 : K)}, x ^ k := by
    rw [← Finset.sum_sdiff ({0} : Finset K).subset_univ, Finset.sum_singleton, zero_pow hk.ne',
      add_zero]
  have hmap : (univ : Finset Kˣ).map ⟨Units.val, Units.val_injective⟩ = univ \ {0} := by
    ext x
    simp only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      exact a.ne_zero
    · intro hx
      exact ⟨Units.mk0 x hx, rfl⟩
  rw [h1, ← hmap, Finset.sum_map]
  exact FiniteField.sum_pow_units K k

/-- Summing `i ^ k` mod `p` over a block of length `p * m` is `m` copies of the sum over
all residues. -/
private theorem giuga_sum_range_mul_zmod (p : ℕ) [NeZero p] (k m : ℕ) :
    ∑ i ∈ range (p * m), ((i : ℕ) : ZMod p) ^ k = m • (∑ x : ZMod p, x ^ k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : p * (m + 1) = p * m + p := by ring
    rw [hsplit, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    have hshift : ∀ i ∈ range p, ((p * m + i : ℕ) : ZMod p) ^ k = ((i : ℕ) : ZMod p) ^ k := by
      intro i _
      push_cast
      simp
    rw [Finset.sum_congr rfl hshift]
    refine Finset.sum_nbij' (fun i => ((i : ℕ) : ZMod p)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_ <;>
      intro a ha <;>
      simp_all [ZMod.val_lt, ZMod.natCast_val, mem_range, Nat.mod_eq_of_lt]

/-- The power sum `∑_{i < p*m} i^k` modulo a prime `p`, for `k ≥ 1`. -/
private theorem giuga_sum_range_pow_mod_prime (p m k : ℕ) (hp : p.Prime) (hk : 0 < k) :
    ((∑ i ∈ range (p * m), i ^ k : ℕ) : ZMod p)
      = if (p - 1) ∣ k then -(m : ZMod p) else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  have hcast : ((∑ i ∈ range (p * m), i ^ k : ℕ) : ZMod p)
      = ∑ i ∈ range (p * m), ((i : ℕ) : ZMod p) ^ k := by
    push_cast
    rfl
  rw [hcast, giuga_sum_range_mul_zmod p k m, giuga_sum_pow_field (ZMod p) k hk, ZMod.card]
  split_ifs with h
  · simp [nsmul_eq_mul]
  · simp

/-- Dropping the vanishing `i = 0` term. -/
private theorem giuga_sum_Ioo_eq_sum_range (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) = ∑ i ∈ range n, i ^ (n - 1) := by
  have hins : range n = insert 0 (Finset.Ioo 0 n) := by
    ext x
    simp only [mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  have h0 : (0 : ℕ) ∉ Finset.Ioo 0 n := by simp
  rw [hins, Finset.sum_insert h0, zero_pow (by omega : n - 1 ≠ 0), zero_add]

/-- Arithmetic identity `n - 1 = (p-1) * m + (m - 1)` when `n = p * m` with `p, m ≥ 1`. -/
private theorem giuga_sub_one_eq (p m : ℕ) (hp : 1 ≤ p) (hm : 1 ≤ m) :
    p * m - 1 = (p - 1) * m + (m - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring_nf
  omega

/-- The residue of `1 + ∑_{i=1}^{n-1} i^{n-1}` modulo a prime divisor `p` of `n`. -/
private theorem giuga_residue_mod_prime (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) :
    ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p)
      = 1 + (if (p - 1) ∣ (n - 1) then -((n / p : ℕ) : ZMod p) else 0) := by
  have hnm : p * (n / p) = n := Nat.mul_div_cancel' hpn
  have hk : 0 < n - 1 := by omega
  have h2 : ((∑ i ∈ range n, i ^ (n - 1) : ℕ) : ZMod p)
      = if (p - 1) ∣ (n - 1) then -((n / p : ℕ) : ZMod p) else 0 := by
    have h3 := giuga_sum_range_pow_mod_prime p (n / p) (n - 1) hp hk
    rwa [hnm] at h3
  rw [giuga_sum_Ioo_eq_sum_range n hn, Nat.cast_add, Nat.cast_one, h2]

private theorem giuga_dvd_sub_one_of_cast_eq_one (p m : ℕ) (hm : 1 ≤ m) (h : ((m : ℕ) : ZMod p) = 1) :
    p ∣ m - 1 := by
  have h1 : ((m : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using h
  have hmod : m ≡ 1 [MOD p] := (ZMod.natCast_eq_natCast_iff _ _ _).mp h1
  exact (Nat.modEq_iff_dvd' hm).mp hmod.symm

private theorem giuga_cast_eq_one_of_dvd_sub_one (p m : ℕ) (hm : 1 ≤ m) (h : p ∣ m - 1) :
    ((m : ℕ) : ZMod p) = 1 := by
  have hmod : (1 : ℕ) ≡ m [MOD p] := (Nat.modEq_iff_dvd' hm).mpr h
  have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  simpa using h1.symm

private theorem giuga_sub_one_dvd_iff (p m : ℕ) (hp : 1 ≤ p) (hm : 1 ≤ m) :
    (p - 1) ∣ (p * m - 1) ↔ (p - 1) ∣ (m - 1) := by
  rw [giuga_sub_one_eq p m hp hm]
  exact ⟨fun h => (Nat.dvd_add_right (dvd_mul_right (p - 1) m)).mp h,
    fun h => Dvd.dvd.add (dvd_mul_right (p - 1) m) h⟩

/-- **Giuga's criterion.** For `n ≥ 2`, the congruence `∑_{i=1}^{n-1} i^{n-1} ≡ -1 (mod n)`
holds if and only if for every prime `p ∣ n` both `p ∣ n/p - 1` and `p - 1 ∣ n/p - 1`. -/
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    n ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) ↔
      ∀ p : ℕ, p.Prime → p ∣ n → p ∣ n / p - 1 ∧ (p - 1) ∣ n / p - 1 := by
  constructor
  · intro hdvd p hp hpn
    have : Fact p.Prime := ⟨hp⟩
    have hnm : p * (n / p) = n := Nat.mul_div_cancel' hpn
    have hm1 : 1 ≤ n / p := Nat.one_le_div_iff hp.pos |>.mpr (Nat.le_of_dvd (by omega) hpn)
    have hz : ((1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr (hpn.trans hdvd)
    rw [giuga_residue_mod_prime n p hn hp hpn] at hz
    by_cases hc : (p - 1) ∣ (n - 1)
    · rw [if_pos hc] at hz
      have hcast : ((n / p : ℕ) : ZMod p) = 1 := (add_neg_eq_zero.mp hz).symm
      refine ⟨giuga_dvd_sub_one_of_cast_eq_one p (n / p) hm1 hcast, ?_⟩
      rw [← hnm] at hc
      exact (giuga_sub_one_dvd_iff p (n / p) hp.one_lt.le hm1).mp hc
    · rw [if_neg hc, add_zero] at hz
      exact absurd hz one_ne_zero
  · intro h
    have hsq : Squarefree n := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro p hp hpp
      have hpn : p ∣ n := dvd_trans (Dvd.intro p rfl) hpp
      have hnm : p * (n / p) = n := Nat.mul_div_cancel' hpn
      have hm1 : 1 ≤ n / p := Nat.one_le_div_iff hp.pos |>.mpr (Nat.le_of_dvd (by omega) hpn)
      have hpm : p ∣ n / p := by
        have : p * p ∣ p * (n / p) := by rwa [hnm]
        exact (mul_dvd_mul_iff_left hp.pos.ne').mp this
      have h1 : p ∣ 1 := by
        have := Nat.dvd_sub hpm (h p hp hpn).1
        simpa [Nat.sub_sub_self hm1] using this
      exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.mp h1)
    have hdvdp : ∀ p ∈ n.primeFactors, p ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) := by
      intro p hpmem
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
      have : Fact p.Prime := ⟨hp⟩
      have hnm : p * (n / p) = n := Nat.mul_div_cancel' hpn
      have hm1 : 1 ≤ n / p := Nat.one_le_div_iff hp.pos |>.mpr (Nat.le_of_dvd (by omega) hpn)
      obtain ⟨hd1, hd2⟩ := h p hp hpn
      have hc : (p - 1) ∣ (n - 1) := by
        rw [← hnm]
        exact (giuga_sub_one_dvd_iff p (n / p) hp.one_lt.le hm1).mpr hd2
      rw [← ZMod.natCast_eq_zero_iff, giuga_residue_mod_prime n p hn hp hpn, if_pos hc,
        giuga_cast_eq_one_of_dvd_sub_one p (n / p) hm1 hd1]
      ring
    calc n = ∏ p ∈ n.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
      _ ∣ 1 + ∑ i ∈ Finset.Ioo 0 n, i ^ (n - 1) :=
          Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hdvdp

