-- Prove2me | solution 1 for BinaryQuadraticForm.kronecker_hurwitz_class_number_relation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:52:20.019205+00:00
-- url     : https://prove2.me/submissions/187f2f06-b8db-4efa-a947-dd4816e24701

import Mathlib
import Definitions.Def_RPLib_S3_KroneckerHurwitz

set_option autoImplicit false

namespace UploadKH

open RamanujanPetersson.S3 RamanujanPetersson.S3.KH

/-- Reduced forms of a negative discriminant `t² - 4n` lie in the box `[1, 4n] × [-4n, 4n] × [1, 4n]`, and the
library's reducedness (`mem_rF`) is the textbook one. -/
theorem mem_box_iff (n : ℕ) (t : ℤ) (hlt : t ^ 2 < 4 * (n : ℤ)) (a b c : ℤ) :
    ((a, b, c) ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
            Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
              r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
                (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1)))) ↔
      (a, b, c) ∈ redForms (t ^ 2 - 4 * n) := by
  rw [mem_rF, Finset.mem_filter, Finset.mem_product, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc,
    Finset.mem_Icc]
  dsimp only
  constructor
  · rintro ⟨⟨⟨ha1, _⟩, _, _⟩, hd, habs, hac, hbd⟩
    obtain ⟨hb1, hb2⟩ := abs_le.1 habs
    refine ⟨hd, ?_, hb2, hac, fun h => hbd (Or.inr h)⟩
    by_contra hcon
    have hbeq : b = -a := by omega
    have habs' : |b| = a := by rw [hbeq, abs_neg, abs_of_pos (by omega)]
    have := hbd (Or.inl habs')
    omega
  · rintro ⟨hd, h1, h2, h3, h4⟩
    have ha0 : 0 < a := by omega
    have hc0 : 0 < c := by omega
    have hb2 : b ^ 2 ≤ a ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 h2) (le_of_lt (by linarith : (0 : ℤ) < a + b))]
    have hac2 : a * a ≤ a * c := mul_le_mul_of_nonneg_left h3 ha0.le
    have h4ac : 4 * a * c ≤ a ^ 2 + 4 * n := by nlinarith [sq_nonneg t]
    have hacn : 3 * (a * c) ≤ 4 * n := by nlinarith
    have hA : a ≤ a * c := by nlinarith
    have hC : c ≤ a * c := by nlinarith
    refine ⟨⟨⟨by omega, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨by omega, by linarith⟩⟩, hd,
      abs_le.2 ⟨by linarith, h2⟩, h3, ?_⟩
    rintro (h | h)
    · rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;> omega
    · exact h4 h

/-- One term: the textbook weighted count of reduced forms is the library's `hurwitzH`. -/
theorem term_eq (n : ℕ) (t : ℤ) (ht : t ^ 2 ≤ 4 * (n : ℤ)) :
    (if t ^ 2 = 4 * (n : ℤ) then (-1 / 12 : ℚ) else
        ∑ r ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
            Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
              r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
                (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))),
          (if r.1 = r.2.1 ∧ r.2.1 = r.2.2 then (1 / 3 : ℚ)
            else if r.2.1 = 0 ∧ r.1 = r.2.2 then 1 / 2 else 1)) =
      hurwitzH (4 * (n : ℤ) - t ^ 2).toNat := by
  classical
  by_cases h0 : t ^ 2 = 4 * (n : ℤ)
  · rw [if_pos h0]
    have : (4 * (n : ℤ) - t ^ 2).toNat = 0 := by rw [h0]; simp
    rw [this]; simp [hurwitzH]
  · rw [if_neg h0]
    have hlt : t ^ 2 < 4 * (n : ℤ) := lt_of_le_of_ne ht h0
    have hNz : (((4 * (n : ℤ) - t ^ 2).toNat : ℕ) : ℤ) = 4 * n - t ^ 2 := Int.toNat_of_nonneg (by linarith)
    have hN0 : (4 * (n : ℤ) - t ^ 2).toNat ≠ 0 := by
      intro h; rw [h] at hNz; push_cast at hNz; linarith
    rw [hurwitzH, if_neg hN0]
    have hD : (-(((4 * (n : ℤ) - t ^ 2).toNat : ℕ) : ℤ)) = t ^ 2 - 4 * n := by rw [hNz]; ring
    rw [hD]
    apply Finset.sum_congr
    · ext ⟨a, b, c⟩
      exact mem_box_iff n t hlt a b c
    · rintro ⟨a, b, c⟩ _
      exact (two_div_stab a b c).symm

theorem main (n : ℕ) (hn : 0 < n) :
    ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)),
      (if t ^ 2 = 4 * (n : ℤ) then (-1 / 12 : ℚ) else
        ∑ r ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
            Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
              r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
                (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))),
          (if r.1 = r.2.1 ∧ r.2.1 = r.2.2 then (1 / 3 : ℚ)
            else if r.2.1 = 0 ∧ r.1 = r.2.2 then 1 / 2 else 1)) =
      2 * ∑ d ∈ n.divisors, (d : ℚ) - ∑ d ∈ n.divisors, ((min d (n / d) : ℕ) : ℚ) := by
  refine Eq.trans (Finset.sum_congr rfl ?_) (kroneckerHurwitz n hn)
  intro t ht
  exact term_eq n t (Finset.mem_filter.1 ht).2

end UploadKH

theorem solution (n : ℕ) (hn : 0 < n) :
    ∑ t ∈ (Finset.Icc (-(2 * n : ℤ)) (2 * n)).filter (fun t : ℤ => t ^ 2 ≤ 4 * (n : ℤ)),
      (if t ^ 2 = 4 * (n : ℤ) then (-1 / 12 : ℚ) else
        ∑ r ∈ (Finset.Icc (1 : ℤ) (4 * n) ×ˢ Finset.Icc (-(4 * n : ℤ)) (4 * n) ×ˢ
            Finset.Icc (1 : ℤ) (4 * n)).filter (fun r : ℤ × ℤ × ℤ =>
              r.2.1 ^ 2 - 4 * r.1 * r.2.2 = t ^ 2 - 4 * n ∧
                (|r.2.1| ≤ r.1 ∧ r.1 ≤ r.2.2 ∧ (|r.2.1| = r.1 ∨ r.1 = r.2.2 → 0 ≤ r.2.1))),
          (if r.1 = r.2.1 ∧ r.2.1 = r.2.2 then (1 / 3 : ℚ)
            else if r.2.1 = 0 ∧ r.1 = r.2.2 then 1 / 2 else 1)) =
      2 * ∑ d ∈ n.divisors, (d : ℚ) - ∑ d ∈ n.divisors, ((min d (n / d) : ℕ) : ℚ) := by
  exact UploadKH.main n hn
