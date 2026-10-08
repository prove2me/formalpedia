-- Prove2me | solution 1 for ErdosStraus242.family_mod863
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T18:12:58.80896+00:00
-- url     : https://prove2.me/submissions/a9b149e1-910d-49e3-b827-c41aeae3c4be

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 863 ∈ ({859, 855, 851, 847, 839, 831, 827, 815, 791, 767, 755, 719, 647, 575, 431} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 863
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 863 * k + n % 863 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- class 859: alpha = 216, g = 1, beta = 215
    have hnform : n = 863 * k + 859 := by omega
    rw [hnform]
    refine ⟨216 * k + 215, 216 * (863 * k + 859), 216 * (216 * k + 215) * (863 * k + 859), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 215 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 859 := by nlinarith
      field_simp
      ring
  · -- class 855: alpha = 216, g = 2, beta = 214
    have hnform : n = 863 * k + 855 := by omega
    rw [hnform]
    refine ⟨216 * k + 214, 216 * (863 * k + 855), 108 * (216 * k + 214) * (863 * k + 855), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 214 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 855 := by nlinarith
      field_simp
      ring
  · -- class 851: alpha = 216, g = 3, beta = 213
    have hnform : n = 863 * k + 851 := by omega
    rw [hnform]
    refine ⟨216 * k + 213, 216 * (863 * k + 851), 72 * (216 * k + 213) * (863 * k + 851), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 213 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 851 := by nlinarith
      field_simp
      ring
  · -- class 847: alpha = 216, g = 4, beta = 212
    have hnform : n = 863 * k + 847 := by omega
    rw [hnform]
    refine ⟨216 * k + 212, 216 * (863 * k + 847), 54 * (216 * k + 212) * (863 * k + 847), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 212 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 847 := by nlinarith
      field_simp
      ring
  · -- class 839: alpha = 216, g = 6, beta = 210
    have hnform : n = 863 * k + 839 := by omega
    rw [hnform]
    refine ⟨216 * k + 210, 216 * (863 * k + 839), 36 * (216 * k + 210) * (863 * k + 839), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 210 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 839 := by nlinarith
      field_simp
      ring
  · -- class 831: alpha = 216, g = 8, beta = 208
    have hnform : n = 863 * k + 831 := by omega
    rw [hnform]
    refine ⟨216 * k + 208, 216 * (863 * k + 831), 27 * (216 * k + 208) * (863 * k + 831), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 208 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 831 := by nlinarith
      field_simp
      ring
  · -- class 827: alpha = 216, g = 9, beta = 207
    have hnform : n = 863 * k + 827 := by omega
    rw [hnform]
    refine ⟨216 * k + 207, 216 * (863 * k + 827), 24 * (216 * k + 207) * (863 * k + 827), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 207 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 827 := by nlinarith
      field_simp
      ring
  · -- class 815: alpha = 216, g = 12, beta = 204
    have hnform : n = 863 * k + 815 := by omega
    rw [hnform]
    refine ⟨216 * k + 204, 216 * (863 * k + 815), 18 * (216 * k + 204) * (863 * k + 815), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 204 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 815 := by nlinarith
      field_simp
      ring
  · -- class 791: alpha = 216, g = 18, beta = 198
    have hnform : n = 863 * k + 791 := by omega
    rw [hnform]
    refine ⟨216 * k + 198, 216 * (863 * k + 791), 12 * (216 * k + 198) * (863 * k + 791), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 198 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 791 := by nlinarith
      field_simp
      ring
  · -- class 767: alpha = 216, g = 24, beta = 192
    have hnform : n = 863 * k + 767 := by omega
    rw [hnform]
    refine ⟨216 * k + 192, 216 * (863 * k + 767), 9 * (216 * k + 192) * (863 * k + 767), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 192 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 767 := by nlinarith
      field_simp
      ring
  · -- class 755: alpha = 216, g = 27, beta = 189
    have hnform : n = 863 * k + 755 := by omega
    rw [hnform]
    refine ⟨216 * k + 189, 216 * (863 * k + 755), 8 * (216 * k + 189) * (863 * k + 755), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 189 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 755 := by nlinarith
      field_simp
      ring
  · -- class 719: alpha = 216, g = 36, beta = 180
    have hnform : n = 863 * k + 719 := by omega
    rw [hnform]
    refine ⟨216 * k + 180, 216 * (863 * k + 719), 6 * (216 * k + 180) * (863 * k + 719), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 180 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 719 := by nlinarith
      field_simp
      ring
  · -- class 647: alpha = 216, g = 54, beta = 162
    have hnform : n = 863 * k + 647 := by omega
    rw [hnform]
    refine ⟨216 * k + 162, 216 * (863 * k + 647), 4 * (216 * k + 162) * (863 * k + 647), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 162 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 647 := by nlinarith
      field_simp
      ring
  · -- class 575: alpha = 216, g = 72, beta = 144
    have hnform : n = 863 * k + 575 := by omega
    rw [hnform]
    refine ⟨216 * k + 144, 216 * (863 * k + 575), 3 * (216 * k + 144) * (863 * k + 575), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 216 * k + 144 := by nlinarith
      have hk2 : (0 : ℚ) < 863 * k + 575 := by nlinarith
      field_simp
      ring
  · -- class 431: alpha = 216, g = 108, beta = 108
    have hnform : n = 863 * k + 431 := by omega
    by_cases hk0 : k = 0
    · have h431 : n = 431 := by omega
      rw [h431]
      refine ⟨108, 46549, 2166762852, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨216 * k + 108, 216 * (863 * k + 431), 2 * (216 * k + 108) * (863 * k + 431), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 216 * k + 108 := by nlinarith
        have hk2 : (0 : ℚ) < 863 * k + 431 := by nlinarith
        field_simp
        ring
