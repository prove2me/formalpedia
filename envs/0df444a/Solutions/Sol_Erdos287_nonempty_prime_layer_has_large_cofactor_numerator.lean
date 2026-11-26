-- Prove2me | solution 1 for Erdos287.nonempty_prime_layer_has_large_cofactor_numerator
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T06:52:42.423975+00:00
-- url     : https://prove2.me/submissions/122dea2f-5237-4388-96c2-a06264e8089e

import Mathlib
import Theorems.Thm_Erdos287_exact_prime_power_in_reduced_denominator

open Finset

set_option autoImplicit false

/-- A nonempty top prime-power layer must have enough cofactors for their
cleared reciprocal numerator to reach the prime. -/
theorem solution (D : Finset ℕ) (M p e : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hD : ∀ n ∈ D, 0 < n ∧ n ≤ M) (hmax : ∀ n ∈ D, padicValNat p n ≤ e)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hT : (D.filter (fun n => padicValNat p n = e)).Nonempty) :
    let T := D.filter (fun n => padicValNat p n = e)
    let A := ∑ n ∈ T, ∏ d ∈ T.erase n, d / p ^ e
    p ∣ A ∧ p ≤ A ∧ A ≤ T.card * (M / p ^ e) ^ (T.card - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  let T := D.filter (fun n => padicValNat p n = e)
  let c (n : ℕ) := n / p ^ e
  let L := ∏ n ∈ T, c n
  let A := ∑ n ∈ T, ∏ d ∈ T.erase n, c d
  change p ∣ A ∧ p ≤ A ∧ A ≤ T.card * (M / p ^ e) ^ (T.card - 1)
  have hc (n : ℕ) (hn : n ∈ T) : 0 < c n ∧ ¬ p ∣ c n := by
    obtain ⟨hnD, hne⟩ := mem_filter.mp hn
    have hpdiv : p ^ e ∣ n := (padicValNat_dvd_iff_le (hD n hnD).1.ne').mpr hne.ge
    refine ⟨Nat.div_pos (Nat.le_of_dvd (hD n hnD).1 hpdiv) (pow_pos hp.pos _), ?_⟩
    intro h
    have hd := (Nat.dvd_div_iff_mul_dvd hpdiv).mp h
    have hnext : p ^ (e + 1) ∣ n := by simpa only [pow_succ, mul_comm] using hd
    have hv := (padicValNat_dvd_iff_le (hD n hnD).1.ne').mp hnext
    omega
  have hL : ¬ p ∣ L := by
    intro hd
    obtain ⟨n, hn, hq⟩ := (hp.prime.dvd_finsetProd_iff c).mp hd
    exact (hc n hn).2 hq
  have hterm (n : ℕ) (hn : n ∈ T) : L / c n = ∏ d ∈ T.erase n, c d := by
    apply Nat.div_eq_of_eq_mul_left (hc n hn).1
    exact (prod_erase_mul T c hn).symm
  have hA : p ∣ A := by
    by_contra hd
    have hnorm := (Erdos287.exact_prime_power_in_reduced_denominator D (fun _ => 1)
      p e L hp he hL (fun n hn => (hD n hn).1) hmax
      (fun n hn hv => dvd_prod_of_mem c (mem_filter.mpr ⟨hn, hv⟩))).2
    have htest : ¬ (p : ℤ) ∣ ∑ n ∈ T, ((L / c n : ℕ) : ℤ) := by
      rw [← Nat.cast_sum, Int.natCast_dvd_natCast]
      have heq : (∑ n ∈ T, L / c n) = A := sum_congr rfl hterm
      simpa only [heq] using hd
    have hv := hnorm (by simpa only [one_mul] using htest)
    have hpval : padicValNat p 1 = 0 := padicValNat.eq_zero_of_not_dvd hp.not_dvd_one
    simp only [Int.cast_one, hsum, Rat.den_one, hpval] at hv
    omega
  have hApos : 0 < A := by
    obtain ⟨n, hn⟩ := hT
    have hpos : 0 < ∏ d ∈ T.erase n, c d :=
      prod_pos fun d hd => (hc d (mem_of_mem_erase hd)).1
    exact hpos.trans_le (single_le_sum (f := fun n => ∏ d ∈ T.erase n, c d)
      (fun _ _ => Nat.zero_le _) hn)
  refine ⟨hA, Nat.le_of_dvd hApos hA, ?_⟩
  calc
    A ≤ ∑ _ ∈ T, (M / p ^ e) ^ (T.card - 1) := by
      apply sum_le_sum
      intro n hn
      have hh := prod_le_pow_card (T.erase n) c (M / p ^ e)
        (fun d hd => Nat.div_le_div_right (hD d (mem_filter.mp (mem_of_mem_erase hd)).1).2)
      simpa only [card_erase_of_mem hn] using hh
    _ = _ := by simp

