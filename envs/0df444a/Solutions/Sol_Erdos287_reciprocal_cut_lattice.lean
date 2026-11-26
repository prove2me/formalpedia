-- Prove2me | solution 1 for Erdos287.reciprocal_cut_lattice
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T08:43:41.066318+00:00
-- url     : https://prove2.me/submissions/3db23362-f184-4e0b-a765-228676239e51

import Mathlib

open Finset

set_option autoImplicit false

private theorem scaled_reciprocal_sum (S : Finset ℕ) (a : ℕ) (ha : 0 < a)
    (hdiv : ∀ n ∈ S, n ∣ a) :
    (∑ n ∈ S, (1 : ℚ) / n) = ((∑ n ∈ S, a / n : ℕ) : ℚ) / a := by
  rw [Nat.cast_sum, Finset.sum_div]
  apply sum_congr rfl
  intro n hn
  have hn₀ : 0 < n := Nat.pos_of_dvd_of_pos (hdiv n hn) ha
  have ha₀ : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn₀.ne'
  have hcast : ((a / n : ℕ) : ℚ) * n = a := by
    exact_mod_cast Nat.div_mul_cancel (hdiv n hn)
  apply (div_eq_div_iff hnq ha₀).mpr
  simpa only [one_mul] using hcast.symm

private theorem denominator_dvd_of_scaled (x a : ℕ) :
    (((x : ℚ) / a).den : ℕ) ∣ a := by
  have he : (x : ℚ) / a = Rat.divInt (x : ℤ) (a : ℤ) := by
    rw [Rat.divInt_eq_div, Int.cast_natCast, Int.cast_natCast]
  rw [he]
  exact Int.natCast_dvd_natCast.mp (Rat.den_dvd _ _)

/-- Splitting a reciprocal sum across a cut yields a bounded integer equation
for any residual target. For target one, the two parts share a divisor lattice. -/
theorem solution (D A B : Finset ℕ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hA : ∀ n ∈ A, n ∣ a) (hB : ∀ n ∈ B, n ∣ b)
    (hdisj : Disjoint A B) (hD : D ⊆ A ∪ B) (r : ℚ)
    (hsum : ∑ n ∈ D, (1 : ℚ) / n = r) :
    let s := ∑ n ∈ D ∩ A, (1 : ℚ) / n
    let t := ∑ n ∈ D ∩ B, (1 : ℚ) / n
    let g := Nat.gcd a b
    (∃ x y : ℕ, s = (x : ℚ) / a ∧ t = (y : ℚ) / b ∧
      x ≤ (∑ n ∈ A, a / n) ∧ y ≤ (∑ n ∈ B, b / n) ∧
      ((Nat.lcm a b : ℕ) : ℚ) * r = (((b / g) * x + (a / g) * y : ℕ) : ℚ)) ∧
    (r = 1 → s.den ∣ g ∧
      ((∑ n ∈ A, (1 : ℚ) / n) < (1 : ℚ) / g → D ⊆ B)) := by
  intro s t g
  have hpartition : D ∩ A ∪ D ∩ B = D := by
    ext n
    simp only [mem_union, mem_inter]
    constructor
    · rintro (⟨hd, _⟩ | ⟨hd, _⟩) <;> exact hd
    · intro hn
      rcases mem_union.mp (hD hn) with h | h
      · exact Or.inl ⟨hn, h⟩
      · exact Or.inr ⟨hn, h⟩
  have hparts : s + t = r := by
    have hsep : Disjoint (D ∩ A) (D ∩ B) :=
      hdisj.mono inter_subset_right inter_subset_right
    have hu := sum_union (f := fun n : ℕ => (1 : ℚ) / n) hsep
    rw [hpartition, hsum] at hu
    exact hu.symm
  let x := ∑ n ∈ D ∩ A, a / n
  let y := ∑ n ∈ D ∩ B, b / n
  have hs : s = (x : ℚ) / a :=
    scaled_reciprocal_sum _ _ ha (fun n hn => hA n (mem_inter.mp hn).2)
  have ht : t = (y : ℚ) / b :=
    scaled_reciprocal_sum _ _ hb (fun n hn => hB n (mem_inter.mp hn).2)
  have hdenA : s.den ∣ a := by rw [hs]; exact denominator_dvd_of_scaled x a
  have hdenB : t.den ∣ b := by rw [ht]; exact denominator_dvd_of_scaled y b
  have hg₀ : 0 < g := Nat.gcd_pos_of_pos_left b ha
  constructor
  · refine ⟨x, y, hs, ht, sum_le_sum_of_subset inter_subset_right,
      sum_le_sum_of_subset inter_subset_right, ?_⟩
    have hla : a * (b / g) = Nat.lcm a b := by
      apply Nat.eq_of_mul_eq_mul_left hg₀
      calc
        g * (a * (b / g)) = a * (b / g * g) := by ac_rfl
        _ = a * b := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right a b)]
        _ = g * Nat.lcm a b := (Nat.gcd_mul_lcm a b).symm
    have hlb : b * (a / g) = Nat.lcm a b := by
      apply Nat.eq_of_mul_eq_mul_left hg₀
      calc
        g * (b * (a / g)) = b * (a / g * g) := by ac_rfl
        _ = a * b := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_left a b), mul_comm]
        _ = g * Nat.lcm a b := (Nat.gcd_mul_lcm a b).symm
    have hla' : (a : ℚ) * ((b / g : ℕ) : ℚ) = (a.lcm b : ℕ) := by exact_mod_cast hla
    have hlb' : (b : ℚ) * ((a / g : ℕ) : ℚ) = (a.lcm b : ℕ) := by exact_mod_cast hlb
    have haq : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    rw [← hparts, hs, ht, mul_add]
    push_cast
    calc
      (a.lcm b : ℕ) * ((x : ℚ) / a) + (a.lcm b : ℕ) * ((y : ℚ) / b) =
          ((a : ℚ) * (b / g : ℕ)) * ((x : ℚ) / a) +
          ((b : ℚ) * (a / g : ℕ)) * ((y : ℚ) / b) := by rw [hla', hlb']
      _ = ((b / g : ℕ) : ℚ) * ((x : ℚ) / a * a) +
          ((a / g : ℕ) : ℚ) * ((y : ℚ) / b * b) := by ac_rfl
      _ = _ := by rw [div_mul_cancel₀ _ haq, div_mul_cancel₀ _ hbq]
  · intro hr
    have hs' : s = 1 - t := by rw [hr] at hparts; linarith only [hparts]
    have hden_t : (1 - t).den ∣ t.den := by
      simpa only [Rat.den_one, Nat.lcm_one_left] using Rat.sub_den_dvd_lcm (1 : ℚ) t
    have hden : s.den ∣ g := Nat.dvd_gcd hdenA (by rw [hs']; exact hden_t.trans hdenB)
    refine ⟨hden, ?_⟩
    intro hsmall n hn
    rcases mem_union.mp (hD hn) with hnA | hnB
    · exfalso
      have hsmall' : s < (1 : ℚ) / g :=
        (sum_le_sum_of_subset_of_nonneg inter_subset_right
          (fun j _ _ => by positivity)).trans_lt hsmall
      have hn₀ : 0 < n := Nat.pos_of_dvd_of_pos (hA n hnA) ha
      have hspos : 0 < s := by
        change 0 < ∑ j ∈ D ∩ A, (1 : ℚ) / j
        have hterm : 0 < (1 : ℚ) / n := by positivity
        exact hterm.trans_le (single_le_sum (f := fun j : ℕ => (1 : ℚ) / j)
          (fun j _ => by positivity) (mem_inter.mpr ⟨hn, hnA⟩))
      have hnump : 0 < s.num := Rat.num_pos.mpr hspos
      have hnum : (1 : ℚ) ≤ s.num := by exact_mod_cast (show (1 : ℤ) ≤ s.num by omega)
      have hdenpos : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
      have hd : (s.den : ℚ) ≤ g := by exact_mod_cast Nat.le_of_dvd hg₀ hden
      have hslo : (1 : ℚ) / g ≤ s := calc
        (1 : ℚ) / g ≤ 1 / s.den := one_div_le_one_div_of_le hdenpos hd
        _ ≤ (s.num : ℚ) / s.den := div_le_div_of_nonneg_right hnum hdenpos.le
        _ = s := s.num_div_den
      exact (not_lt_of_ge hslo) hsmall'
    · exact hnB

