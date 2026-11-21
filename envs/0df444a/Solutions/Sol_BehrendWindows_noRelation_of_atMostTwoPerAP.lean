-- Prove2me | solution 1 for BehrendWindows.noRelation_of_atMostTwoPerAP
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:59:30.970186+00:00
-- url     : https://prove2.me/submissions/1940c1a6-144c-4176-a7f3-92a82b1541d0

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP
import Definitions.Def_BehrendWindows_NoRelation

open BehrendWindows

/-- Three distinct positions of an `m`-term progression, in any order, cannot all be in `T`. -/
lemma BehrendWindows_three_positions {T : Finset ℤ} {m : ℕ} (h : AtMostTwoPerAP T m)
    (a d : ℤ) (hd : d ≠ 0) (p q r : ℕ) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpm : p < m) (hqm : q < m) (hrm : r < m)
    (hp : a + p * d ∈ T) (hq : a + q * d ∈ T) (hr : a + r * d ∈ T) : False := by
  rcases lt_or_gt_of_ne hpq with h1 | h1 <;> rcases lt_or_gt_of_ne hpr with h2 | h2 <;>
    rcases lt_or_gt_of_ne hqr with h3 | h3 <;>
    first
    | exact h a d hd p q r (by omega) (by omega) (by omega) ⟨hp, hq, hr⟩
    | exact h a d hd p r q (by omega) (by omega) (by omega) ⟨hp, hr, hq⟩
    | exact h a d hd q p r (by omega) (by omega) (by omega) ⟨hq, hp, hr⟩
    | exact h a d hd q r p (by omega) (by omega) (by omega) ⟨hq, hr, hp⟩
    | exact h a d hd r p q (by omega) (by omega) (by omega) ⟨hr, hp, hq⟩
    | exact h a d hd r q p (by omega) (by omega) (by omega) ⟨hr, hq, hp⟩

theorem solution {T : Finset ℤ} {L : ℕ}
    (h : AtMostTwoPerAP T (2 * L + 1)) : NoRelation T L := by
  intro s₁ h1 s₂ h2 s₃ h3 n12 n13 n23 i j hi hj hij hiL hjL heq
  have hgpos : 0 < Int.gcd i j := Int.gcd_pos_of_ne_zero_left j hi
  obtain ⟨i', hi'⟩ := Int.gcd_dvd_left (a := i) (b := j)
  obtain ⟨j', hj'⟩ := Int.gcd_dvd_right (a := i) (b := j)
  set g : ℤ := (Int.gcd i j : ℤ) with hg
  have hg0 : 0 < g := by rw [hg]; exact_mod_cast hgpos
  have hcop : IsCoprime i' j' := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have e := Int.gcd_mul_left g i' j'
    rw [← hi', ← hj'] at e
    have hga : g.natAbs = Int.gcd i j := by rw [hg]; simp
    rw [hga] at e
    have : Int.gcd i j * Int.gcd i' j' = Int.gcd i j * 1 := by
      rw [mul_one]; exact e.symm
    exact Nat.eq_of_mul_eq_mul_left hgpos this
  have hi'0 : i' ≠ 0 := by rintro rfl; simp at hi'; exact hi hi'
  have hj'0 : j' ≠ 0 := by rintro rfl; simp at hj'; exact hj hj'
  have hij' : i' ≠ j' := by rintro rfl; exact hij (hi'.trans hj'.symm)
  -- cancel the gcd
  have hrel : j' * (s₂ - s₁) = i' * (s₃ - s₁) := by
    have : g * (j' * (s₂ - s₁) - i' * (s₃ - s₁)) = 0 := by
      rw [hi', hj'] at heq; linear_combination heq
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hg0.ne'
    · linarith
  have hdvd : i' ∣ s₂ - s₁ := by
    have : i' ∣ (s₂ - s₁) * j' := ⟨s₃ - s₁, by linarith [hrel]⟩
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨e, he⟩ := hdvd
  have he3 : s₃ - s₁ = j' * e := by
    have : i' * (s₃ - s₁ - j' * e) = 0 := by linear_combination -hrel + j' * he
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hi'0
    · linarith
  have he0 : e ≠ 0 := by rintro rfl; apply n12; linarith [he]
  -- bounds |i'| ≤ L, |j'| ≤ L
  have habs_i : |i'| ≤ L := by
    have : |i| = g * |i'| := by rw [hi', abs_mul, abs_of_pos hg0]
    nlinarith [abs_nonneg i']
  have habs_j : |j'| ≤ L := by
    have : |j| = g * |j'| := by rw [hj', abs_mul, abs_of_pos hg0]
    nlinarith [abs_nonneg j']
  obtain ⟨hi1, hi2⟩ := abs_le.mp habs_i
  obtain ⟨hj1, hj2⟩ := abs_le.mp habs_j
  obtain ⟨p1, hp1⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ L + i' by linarith)
  obtain ⟨p2, hp2⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ L + j' by linarith)
  refine BehrendWindows_three_positions h (s₁ - L * e) e he0 L p1 p2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_ ?_ ?_
  · convert h1 using 1; ring
  · convert h2 using 1; rw [← hp1]; linear_combination -he
  · convert h3 using 1; rw [← hp2]; linear_combination -he3
