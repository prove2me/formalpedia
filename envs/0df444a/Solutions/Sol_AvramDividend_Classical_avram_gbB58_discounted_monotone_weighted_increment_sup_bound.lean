-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB58_discounted_monotone_weighted_increment_sup_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:52:06.292237+00:00
-- url     : https://prove2.me/submissions/727cc8e0-cad3-4785-a940-d651a1445f21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB53_physical_discounted_mesh_abel_telescope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
/-- Discounted monotone weights preserve a sup-norm bound on centred increments. -/
theorem solution (m : ℕ) (a b : ℕ → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (ha : Antitone a) (ha0 : a 0 ≤ 1)
    (ham : 0 ≤ a m) (hb0 : b 0 = 0)
    (hb : ∀ i ≤ m + 1, |b i| ≤ ε) :
    |(Finset.range (m + 1)).sum (fun i =>
      a i * (b (i + 1) - b i))| ≤ ε := by
  have hAbel := avram_gbB53_physical_discounted_mesh_abel_telescope m a b
  have hDiff (i : ℕ) : 0 ≤ a i - a (i + 1) :=
    sub_nonneg.mpr (ha (Nat.le_succ i))
  have hSumAux : ∀ k : ℕ, (Finset.range k).sum (fun i =>
      a i - a (i + 1)) = a 0 - a k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have hSum := hSumAux m
  have hBupper (i : ℕ) (hi : i ≤ m + 1) : b i ≤ ε :=
    (abs_le.mp (hb i hi)).2
  have hBlower (i : ℕ) (hi : i ≤ m + 1) : -ε ≤ b i :=
    (abs_le.mp (hb i hi)).1
  have hUpper : (Finset.range (m + 1)).sum (fun i =>
      a i * (b (i + 1) - b i)) ≤ ε := by
    rw [hAbel, hb0, mul_zero, sub_zero]
    have hEnd := mul_le_mul_of_nonneg_left (hBupper (m + 1) le_rfl) ham
    have hBound := Finset.sum_le_sum
      (s := Finset.range m) (fun i hi =>
        mul_le_mul_of_nonneg_left
          (hBupper (i + 1) (by have hi' : i < m := Finset.mem_range.mp hi; omega)) (hDiff i))
    have hTotal :
        (Finset.range m).sum (fun i =>
          (a i - a (i + 1)) * ε) = (a 0 - a m) * ε := by
      rw [← Finset.sum_mul, hSum]
    rw [hTotal] at hBound
    nlinarith [mul_nonneg (sub_nonneg.mpr
      (ha (Nat.zero_le m))) hε]
  have hLower : -ε ≤ (Finset.range (m + 1)).sum (fun i =>
      a i * (b (i + 1) - b i)) := by
    rw [hAbel, hb0, mul_zero, sub_zero]
    have hEnd := mul_le_mul_of_nonneg_left
      (hBlower (m + 1) le_rfl) ham
    have hBound := Finset.sum_le_sum
      (s := Finset.range m) (fun i hi =>
        mul_le_mul_of_nonneg_left
          (hBlower (i + 1) (by have hi' : i < m := Finset.mem_range.mp hi; omega)) (hDiff i))
    have hTotal :
        (Finset.range m).sum (fun i =>
          (a i - a (i + 1)) * (-ε)) =
            (a 0 - a m) * (-ε) := by
      rw [← Finset.sum_mul, hSum]
    rw [hTotal] at hBound
    nlinarith [mul_nonneg (sub_nonneg.mpr
      (ha (Nat.zero_le m))) hε]
  exact abs_le.mpr ⟨hLower, hUpper⟩
