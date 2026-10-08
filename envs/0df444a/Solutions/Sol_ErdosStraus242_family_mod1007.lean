-- Prove2me | solution 1 for ErdosStraus242.family_mod1007
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T23:42:34.38104+00:00
-- url     : https://prove2.me/submissions/90575fa3-940c-4280-9b18-cc3b663c2e03

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

open ErdosStraus242

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 1007 ∈ ({1003, 999, 995, 991, 983, 979, 971, 959, 951, 935, 923, 895, 863, 839, 755, 671, 503} : Finset ℕ)) : IsErdosStraus n := by
  let k := n / 1007
  have hk : 0 ≤ k := by dsimp [k]; omega
  have hdiv : n = 1007 * k + n % 1007 := by dsimp [k]; omega
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod
  rcases hmod with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · -- class 1003: alpha = 252, g = 1, beta = 251
    have hnform : n = 1007 * k + 1003 := by omega
    rw [hnform]
    refine ⟨252 * k + 251, 252 * (1007 * k + 1003), 252 * (252 * k + 251) * (1007 * k + 1003), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 251 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 1003 := by nlinarith
      field_simp
      ring
  · -- class 999: alpha = 252, g = 2, beta = 250
    have hnform : n = 1007 * k + 999 := by omega
    rw [hnform]
    refine ⟨252 * k + 250, 252 * (1007 * k + 999), 126 * (252 * k + 250) * (1007 * k + 999), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 250 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 999 := by nlinarith
      field_simp
      ring
  · -- class 995: alpha = 252, g = 3, beta = 249
    have hnform : n = 1007 * k + 995 := by omega
    rw [hnform]
    refine ⟨252 * k + 249, 252 * (1007 * k + 995), 84 * (252 * k + 249) * (1007 * k + 995), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 249 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 995 := by nlinarith
      field_simp
      ring
  · -- class 991: alpha = 252, g = 4, beta = 248
    have hnform : n = 1007 * k + 991 := by omega
    rw [hnform]
    refine ⟨252 * k + 248, 252 * (1007 * k + 991), 63 * (252 * k + 248) * (1007 * k + 991), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 248 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 991 := by nlinarith
      field_simp
      ring
  · -- class 983: alpha = 252, g = 6, beta = 246
    have hnform : n = 1007 * k + 983 := by omega
    rw [hnform]
    refine ⟨252 * k + 246, 252 * (1007 * k + 983), 42 * (252 * k + 246) * (1007 * k + 983), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 246 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 983 := by nlinarith
      field_simp
      ring
  · -- class 979: alpha = 252, g = 7, beta = 245
    have hnform : n = 1007 * k + 979 := by omega
    rw [hnform]
    refine ⟨252 * k + 245, 252 * (1007 * k + 979), 36 * (252 * k + 245) * (1007 * k + 979), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 245 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 979 := by nlinarith
      field_simp
      ring
  · -- class 971: alpha = 252, g = 9, beta = 243
    have hnform : n = 1007 * k + 971 := by omega
    rw [hnform]
    refine ⟨252 * k + 243, 252 * (1007 * k + 971), 28 * (252 * k + 243) * (1007 * k + 971), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 243 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 971 := by nlinarith
      field_simp
      ring
  · -- class 959: alpha = 252, g = 12, beta = 240
    have hnform : n = 1007 * k + 959 := by omega
    rw [hnform]
    refine ⟨252 * k + 240, 252 * (1007 * k + 959), 21 * (252 * k + 240) * (1007 * k + 959), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 240 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 959 := by nlinarith
      field_simp
      ring
  · -- class 951: alpha = 252, g = 14, beta = 238
    have hnform : n = 1007 * k + 951 := by omega
    rw [hnform]
    refine ⟨252 * k + 238, 252 * (1007 * k + 951), 18 * (252 * k + 238) * (1007 * k + 951), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 238 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 951 := by nlinarith
      field_simp
      ring
  · -- class 935: alpha = 252, g = 18, beta = 234
    have hnform : n = 1007 * k + 935 := by omega
    rw [hnform]
    refine ⟨252 * k + 234, 252 * (1007 * k + 935), 14 * (252 * k + 234) * (1007 * k + 935), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 234 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 935 := by nlinarith
      field_simp
      ring
  · -- class 923: alpha = 252, g = 21, beta = 231
    have hnform : n = 1007 * k + 923 := by omega
    rw [hnform]
    refine ⟨252 * k + 231, 252 * (1007 * k + 923), 12 * (252 * k + 231) * (1007 * k + 923), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 231 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 923 := by nlinarith
      field_simp
      ring
  · -- class 895: alpha = 252, g = 28, beta = 224
    have hnform : n = 1007 * k + 895 := by omega
    rw [hnform]
    refine ⟨252 * k + 224, 252 * (1007 * k + 895), 9 * (252 * k + 224) * (1007 * k + 895), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 224 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 895 := by nlinarith
      field_simp
      ring
  · -- class 863: alpha = 252, g = 36, beta = 216
    have hnform : n = 1007 * k + 863 := by omega
    rw [hnform]
    refine ⟨252 * k + 216, 252 * (1007 * k + 863), 7 * (252 * k + 216) * (1007 * k + 863), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 216 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 863 := by nlinarith
      field_simp
      ring
  · -- class 839: alpha = 252, g = 42, beta = 210
    have hnform : n = 1007 * k + 839 := by omega
    rw [hnform]
    refine ⟨252 * k + 210, 252 * (1007 * k + 839), 6 * (252 * k + 210) * (1007 * k + 839), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 210 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 839 := by nlinarith
      field_simp
      ring
  · -- class 755: alpha = 252, g = 63, beta = 189
    have hnform : n = 1007 * k + 755 := by omega
    rw [hnform]
    refine ⟨252 * k + 189, 252 * (1007 * k + 755), 4 * (252 * k + 189) * (1007 * k + 755), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 189 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 755 := by nlinarith
      field_simp
      ring
  · -- class 671: alpha = 252, g = 84, beta = 168
    have hnform : n = 1007 * k + 671 := by omega
    rw [hnform]
    refine ⟨252 * k + 168, 252 * (1007 * k + 671), 3 * (252 * k + 168) * (1007 * k + 671), ?_, ?_, ?_, ?_⟩
    · omega
    · nlinarith
    · nlinarith
    · push_cast
      have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
      have hk1 : (0 : ℚ) < 252 * k + 168 := by nlinarith
      have hk2 : (0 : ℚ) < 1007 * k + 671 := by nlinarith
      field_simp
      ring
  · -- class 503: alpha = 252, g = 126, beta = 126
    have hnform : n = 1007 * k + 503 := by omega
    by_cases hk0 : k = 0
    · have h503 : n = 503 := by omega
      rw [h503]
      refine ⟨126, 63379, 4016834262, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · norm_num
    · have hk1 : 1 ≤ k := by omega
      rw [hnform]
      refine ⟨252 * k + 126, 252 * (1007 * k + 503), 2 * (252 * k + 126) * (1007 * k + 503), ?_, ?_, ?_, ?_⟩
      · omega
      · nlinarith
      · exact Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      · push_cast
        have hkq : (0 : ℚ) ≤ k := Nat.cast_nonneg _
        have hk1 : (0 : ℚ) < 252 * k + 126 := by nlinarith
        have hk2 : (0 : ℚ) < 1007 * k + 503 := by nlinarith
        field_simp
        ring
