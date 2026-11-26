-- Prove2me | solution 1 for Erdos287.large_prime_product_divides_reciprocal_denominator
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:15:54.753252+00:00
-- url     : https://prove2.me/submissions/afcf21a8-f566-4cdb-afc8-bf0a8ab5fa87

import Mathlib
import Theorems.Thm_Erdos287_exact_prime_power_in_reduced_denominator

open Finset

set_option autoImplicit false

/-- Every tested large prime with an included multiple contributes to the
reduced denominator of the reciprocal sum. -/
theorem solution (D P : Finset ℕ) (M : ℕ)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M)
    (hP : ∀ p ∈ P, p.Prime)
    (hsmall : ∀ p ∈ P, (M / p) * Nat.lcmUpto (M / p) < p)
    (hmem : ∀ p ∈ P, ∃ n ∈ D, p ∣ n) :
    (∏ p ∈ P, p) ∣ (∑ n ∈ D, (1 : ℚ) / n).den := by
  let x := ∑ n ∈ D, (1 : ℚ) / n
  change (∏ p ∈ P, p) ∣ x.den
  have hprime (p : ℕ) (hpP : p ∈ P) : p ∣ x.den := by
    have hp := hP p hpP
    have : Fact p.Prime := ⟨hp⟩
    let B := M / p
    let L := Nat.lcmUpto B
    let S := D.filter (fun n => padicValNat p n = 1)
    have hBL : B * L < p := hsmall p hpP
    have hLpos : 0 < L := Nat.lcmUpto_pos B
    have hBp : B < p := (Nat.le_mul_of_pos_right B hLpos).trans_lt hBL
    have hMp : M < p * p := (Nat.div_lt_iff_lt_mul hp.pos).mp hBp
    have hmax (n : ℕ) (hn : n ∈ D) : padicValNat p n ≤ 1 := by
      by_contra! h
      have hd : p ^ 2 ∣ n := (padicValNat_dvd_iff_le (hD n hn).1.ne').mpr (by omega)
      have hle := (Nat.le_of_dvd (hD n hn).1 hd).trans (hD n hn).2
      rw [pow_two] at hle
      exact (not_le_of_gt hMp) hle
    have hfit (n : ℕ) (hn : n ∈ D) (hd : p ∣ n) : n / p ∈ Icc 1 B := by
      refine mem_Icc.mpr ⟨?_, Nat.div_le_div_right (hD n hn).2⟩
      exact Nat.div_pos (Nat.le_of_dvd (hD n hn).1 hd) hp.pos
    have hpdvd (n : ℕ) (hn : n ∈ D) : p ∣ n ↔ 1 ≤ padicValNat p n := by
      simpa only [pow_one] using (padicValNat_dvd_iff_le (n := 1) (hD n hn).1.ne')
    have hcoe (n : ℕ) (hn : n ∈ S) : n / p ∈ Icc 1 B := by
      obtain ⟨hnD, hv⟩ := mem_filter.mp hn
      exact hfit n hnD ((hpdvd n hnD).mpr hv.ge)
    have hL : ¬ p ∣ L := by
      intro hd
      have hd' := hd.trans ((Icc 1 B).lcm_dvd_prod id)
      obtain ⟨j, hj, hpj⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd'
      have hj' := mem_Icc.mp hj
      exact (not_le_of_gt (hj'.2.trans_lt hBp)) (Nat.le_of_dvd hj'.1 hpj)
    have hinj : Set.InjOn (fun n : ℕ => n / p) (↑S : Set ℕ) := by
      intro a ha b hb heq
      obtain ⟨haD, haV⟩ := mem_filter.mp ha
      obtain ⟨hbD, hbV⟩ := mem_filter.mp hb
      have haE := Nat.div_mul_cancel ((hpdvd a haD).mpr haV.ge)
      have hbE := Nat.div_mul_cancel ((hpdvd b hbD).mpr hbV.ge)
      exact haE.symm.trans ((congrArg (· * p) heq).trans hbE)
    let A := ∑ n ∈ S, L / (n / p)
    have hbound : A < p := by
      have hs : S.image (fun n => n / p) ⊆ Icc 1 B := image_subset_iff.mpr hcoe
      apply lt_of_le_of_lt _ hBL
      calc
        A = ∑ c ∈ S.image (fun n => n / p), L / c := (sum_image hinj).symm
        _ ≤ ∑ c ∈ Icc 1 B, L / c := sum_le_sum_of_subset hs
        _ ≤ ∑ _ ∈ Icc 1 B, L := sum_le_sum fun _ _ => Nat.div_le_self _ _
        _ = B * L := by simp
    have hApos : 0 < A := by
      obtain ⟨n, hn, hd⟩ := hmem p hpP
      have hnS : n ∈ S := mem_filter.mpr ⟨hn, le_antisymm (hmax n hn) ((hpdvd n hn).mp hd)⟩
      have hcn : n / p ∣ L := Finset.dvd_lcm (hcoe n hnS)
      have hpos : 0 < L / (n / p) :=
        Nat.div_pos (Nat.le_of_dvd hLpos hcn) (mem_Icc.mp (hcoe n hnS)).1
      exact hpos.trans_le (single_le_sum (f := fun n => L / (n / p)) (fun _ _ => Nat.zero_le _) hnS)
    have hA : ¬ p ∣ A := fun hd => (not_le_of_gt hbound) (Nat.le_of_dvd hApos hd)
    have hA' : ¬ (p : ℤ) ∣ ∑ n ∈ S, ((L / (n / p) : ℕ) : ℤ) := by
      simpa only [← Nat.cast_sum, Int.natCast_dvd_natCast] using hA
    have hval := (Erdos287.exact_prime_power_in_reduced_denominator D (fun _ => 1)
      p 1 L hp le_rfl hL (fun n hn => (hD n hn).1) hmax (by
        intro n hn hv
        rw [pow_one]
        exact Finset.dvd_lcm (hcoe n (mem_filter.mpr ⟨hn, hv⟩)))).2
        (by simpa only [pow_one, one_mul] using hA')
    have hxval : padicValNat p x.den = 1 := by simpa only [x, Int.cast_one] using hval
    simpa only [pow_one] using
      (padicValNat_dvd_iff_le (p := p) (n := 1) x.den_ne_zero).mpr hxval.ge
  apply Int.natCast_dvd_natCast.mp
  rw [Nat.cast_prod]
  refine Finset.prod_dvd_of_coprime ?_ fun p hp => Int.natCast_dvd_natCast.mpr (hprime p hp)
  intro p hp q hq hpq
  exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)

