-- Prove2me | solution 1 for BlockCycleRotation.sum_allShifts_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:05:50.765273+00:00
-- url     : https://prove2.me/submissions/34e7d7c3-3edf-48ad-9989-677b8d2a7c76

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem mem_shifts {n k : ℕ} :
    k ∈ shifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n ∧ Nat.gcd n k = 1 := by
  simp [shifts]

theorem mem_allShifts {n k : ℕ} : k ∈ allShifts n ↔ k ≤ n ∧ 1 ≤ k ∧ 2 * k ≤ n := by
  simp [allShifts]

end BlockCycleRotation

open BlockCycleRotation in
/-- **Classifying shifts by their gcd with `n`.**  Every shift is `g·k'` for a
unique divisor `g` of `n` and a shift `k'` of `n/g` coprime to it. -/
theorem solution {n : ℕ} (hn : 0 < n) (F : ℕ → ℕ → ℕ) :
    ∑ k ∈ allShifts n, F (Nat.gcd n k) (k / Nat.gcd n k)
      = ∑ g ∈ n.divisors, ∑ k' ∈ shifts (n / g), F g k':= by
  rw [Finset.sum_sigma']
  refine Finset.sum_bij'
    (i := fun k _ => (⟨Nat.gcd n k, k / Nat.gcd n k⟩ : (_ : ℕ) × ℕ))
    (j := fun p _ => p.1 * p.2) ?_ ?_ ?_ ?_ ?_
  · -- forward map lands correctly
    intro k hk
    obtain ⟨hkn, hk1, hk2⟩ := mem_allShifts.1 hk
    have hg : 0 < Nat.gcd n k := Nat.gcd_pos_of_pos_left _ hn
    have hgn : Nat.gcd n k ∣ n := Nat.gcd_dvd_left _ _
    have hgk : Nat.gcd n k ∣ k := Nat.gcd_dvd_right _ _
    simp only [Finset.mem_sigma, Nat.mem_divisors]
    refine ⟨⟨hgn, hn.ne'⟩, mem_shifts.2 ⟨?_, ?_, ?_, ?_⟩⟩
    · exact Nat.div_le_div_right hkn
    · exact Nat.one_le_div_iff hg |>.2 (Nat.le_of_dvd (by omega) hgk)
    · calc 2 * (k / Nat.gcd n k) = 2 * k / Nat.gcd n k := (Nat.mul_div_assoc 2 hgk).symm
        _ ≤ n / Nat.gcd n k := Nat.div_le_div_right hk2
    · exact Nat.coprime_div_gcd_div_gcd hg
  · -- inverse map lands correctly
    rintro ⟨g, k'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hgn, -⟩, hk'⟩ := hp
    obtain ⟨-, hk'1, hk'2, -⟩ := mem_shifts.1 hk'
    have hg : 0 < g := Nat.pos_of_dvd_of_pos hgn hn
    have hmul : g * (n / g) = n := Nat.mul_div_cancel' hgn
    rw [mem_allShifts]
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [hmul, hk'2]
    · exact Nat.mul_pos hg hk'1
    · nlinarith [hmul, hk'2]
  · -- left inverse
    intro k hk
    obtain ⟨-, hk1, -⟩ := mem_allShifts.1 hk
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_right n k)
  · -- right inverse
    rintro ⟨g, k'⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨hgn, -⟩, hk'⟩ := hp
    obtain ⟨-, -, -, hcop⟩ := mem_shifts.1 hk'
    have hg : 0 < g := Nat.pos_of_dvd_of_pos hgn hn
    have hmul : g * (n / g) = n := Nat.mul_div_cancel' hgn
    have hgcd : Nat.gcd n (g * k') = g := by
      conv_lhs => rw [← hmul]
      rw [Nat.gcd_mul_left, hcop, mul_one]
    simp only [hgcd]
    congr 1
    rw [Nat.mul_div_cancel_left _ hg]
  · intro k _
    rfl
