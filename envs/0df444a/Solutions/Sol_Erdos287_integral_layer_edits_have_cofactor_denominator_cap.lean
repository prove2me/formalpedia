-- Prove2me | solution 1 for Erdos287.integral_layer_edits_have_cofactor_denominator_cap
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T14:40:39.851876+00:00
-- url     : https://prove2.me/submissions/21ccc578-7a37-4feb-bf45-175aa83832e1

import Mathlib

open Finset

set_option autoImplicit false

private theorem signed_reciprocal_sum_cap (D : Finset ℕ) (sign : ℕ → ℤ) (L : ℕ)
    (hD : ∀ n ∈ D, n ∣ L) : (∑ n ∈ D, (sign n : ℚ) / n).den ∣ L := by
  classical
  induction D using Finset.induction_on with
  | empty => simp
  | insert n D hnot ih =>
    rw [sum_insert hnot]
    have hn : ((sign n : ℚ) / n).den ∣ n := by
      have hr : (sign n : ℚ) / n = Rat.divInt (sign n) (n : ℤ) := by
        rw [Rat.divInt_eq_div, Int.cast_natCast]
      rw [hr]
      exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _)
    exact (Rat.add_den_dvd_lcm _ _).trans (Nat.lcm_dvd
      (hn.trans (hD n (mem_insert_self _ _))) (ih fun k hk => hD k (mem_insert_of_mem hk)))

/-- Signed reciprocal edits whose large factors already cancel can only move a
sum on the lattice from their common cofactor denominator. -/
theorem solution (D : Finset ℕ) (sign : ℕ → ℤ) (s t : ℚ) (C P : ℕ) (hC : 0 < C)
    (hD : ∀ n ∈ D, n ∣ C * P) (hs : s.den.Coprime P) (ht : t.den.Coprime P)
    (hedit : s - t = ∑ n ∈ D, (sign n : ℚ) / n) :
    (s - t).den ∣ C ∧ (s = t ∨ 1 ≤ |s - t| * (C : ℚ)) := by
  have hmul : (s - t).den ∣ C * P := by
    rw [hedit]
    exact signed_reciprocal_sum_cap D sign (C * P) hD
  have hcop : (s - t).den.Coprime P :=
    (hs.mul_left ht).coprime_dvd_left (Rat.sub_den_dvd _ _)
  have hdiv : (s - t).den ∣ C := hcop.dvd_of_dvd_mul_right hmul
  refine ⟨hdiv, ?_⟩
  by_cases he : s = t
  · exact Or.inl he
  · right
    let u := s - t
    have hu : u ≠ 0 := sub_ne_zero.mpr he
    have hn : (1 : ℚ) ≤ |(u.num : ℚ)| := by
      have habs : (1 : ℤ) ≤ |u.num| := by
        have hz : u.num ≠ 0 := Rat.num_ne_zero.mpr hu
        exact Int.add_one_le_of_lt (abs_pos.mpr hz)
      have hcast : (1 : ℚ) ≤ ((|u.num| : ℤ) : ℚ) := by exact_mod_cast habs
      simpa only [Int.cast_abs] using hcast
    have hd : (0 : ℚ) < u.den := by exact_mod_cast u.den_pos
    have hc : (u.den : ℚ) ≤ C := by exact_mod_cast Nat.le_of_dvd hC hdiv
    have hnum : u * (u.den : ℚ) = (u.num : ℚ) := (eq_div_iff hd.ne').mp (Rat.num_div_den u).symm
    change 1 ≤ |u| * C
    calc
      1 ≤ |(u.num : ℚ)| := hn
      _ = |u * u.den| := by rw [hnum]
      _ = |u| * u.den := by rw [abs_mul, abs_of_pos hd]
      _ ≤ |u| * C := mul_le_mul_of_nonneg_left hc (abs_nonneg _)

