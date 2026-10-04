-- Prove2me | solution 1 for ErdosStraus242.family_mod779
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T09:38:29.44517+00:00
-- url     : https://prove2.me/submissions/4ef66069-9767-43a9-8089-c2fdc8a0eb32

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 779 ∈ ({775, 767, 759, 727, 719, 623, 519} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 779
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 779 * k + n % 779 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h
  · -- class 775: alpha = 195, g = 1, beta = 194
    have hnform : n = 779 * k + 775 := by omega
    rw [hnform]
    refine ⟨195 * k + 194, 195 * (779 * k + 775), 195 * (195 * k + 194) * (779 * k + 775), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 195 * k + 194 := by nlinarith
      have hk2 : (0 : ℚ) < 779 * k + 775 := by nlinarith
      field_simp
      ring
  · -- class 767: alpha = 195, g = 3, beta = 192
    have hnform : n = 779 * k + 767 := by omega
    rw [hnform]
    refine ⟨195 * k + 192, 195 * (779 * k + 767), 65 * (195 * k + 192) * (779 * k + 767), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 195 * k + 192 := by nlinarith
      have hk2 : (0 : ℚ) < 779 * k + 767 := by nlinarith
      field_simp
      ring
  · -- class 759: alpha = 195, g = 5, beta = 190
    have hnform : n = 779 * k + 759 := by omega
    rw [hnform]
    refine ⟨195 * k + 190, 195 * (779 * k + 759), 39 * (195 * k + 190) * (779 * k + 759), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 195 * k + 190 := by nlinarith
      have hk2 : (0 : ℚ) < 779 * k + 759 := by nlinarith
      field_simp
      ring
  · -- class 727: alpha = 195, g = 13, beta = 182
    have hnform : n = 779 * k + 727 := by omega
    rw [hnform]
    refine ⟨195 * k + 182, 195 * (779 * k + 727), 15 * (195 * k + 182) * (779 * k + 727), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 195 * k + 182 := by nlinarith
      have hk2 : (0 : ℚ) < 779 * k + 727 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 195, g = 15, beta = 180
    have hnform : n = 779 * k + 719 := by omega
    rw [hnform]
    refine ⟨195 * k + 180, 195 * (779 * k + 719), 13 * (195 * k + 180) * (779 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 195 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 779 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 623: alpha = 195, g = 39, beta = 156
    have hnform : n = 779 * k + 623 := by omega
    rw [hnform]
    refine ⟨195 * k + 156, 195 * (779 * k + 623), 5 * (195 * k + 156) * (779 * k + 623), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 195 * k + 156 := by nlinarith
      have hk2 : (0 : ℚ) < 779 * k + 623 := by nlinarith
      field_simp
      ring
  · -- class 519: alpha = 195, g = 65, beta = 130
    have hnform : n = 779 * k + 519 := by omega
    rw [hnform]
    refine ⟨195 * k + 130, 195 * (779 * k + 519), 3 * (195 * k + 130) * (779 * k + 519), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 195 * k + 130 := by nlinarith
      have hk2 : (0 : ℚ) < 779 * k + 519 := by nlinarith
      field_simp
      ring
