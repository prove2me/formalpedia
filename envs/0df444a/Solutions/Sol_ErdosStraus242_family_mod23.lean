-- Prove2me | solution 1 for ErdosStraus242.family_mod23
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T20:49:18.803599+00:00
-- url     : https://prove2.me/submissions/b643b3de-f804-46ad-bb39-7bc94e4fa8f9

import Definitions.Def_ErdosStraus242
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic

open ErdosStraus242

/-- Clearing denominators: a natural-number identity certifies the rational one. -/
private theorem es_key (n x y z : ℕ) (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : 4 * (x * y * z) = n * (y * z + x * z + x * y)) :
    (4 / n : ℚ) = 1 / x + 1 / y + 1 / z := by
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hx' : (x : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hx.ne'
  have hy' : (y : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hy.ne'
  have hz' : (z : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hz.ne'
  have h' : (4 : ℚ) * (x * y * z) = n * (y * z + x * z + x * y) := by
    exact_mod_cast congrArg (fun t : ℕ => (t : ℚ)) h
  field_simp
  ring_nf
  ring_nf at h'
  linarith [h']

/-- An increasing triple satisfying the cleared identity witnesses the property. -/
private theorem witness (n x y z : ℕ) (hn : 0 < n) (h1 : 1 ≤ x) (h2 : x < y) (h3 : y < z)
    (h : 4 * (x * y * z) = n * (y * z + x * z + x * y)) : IsErdosStraus n :=
  ⟨x, y, z, h1, h2, h3, es_key n x y z hn h1 (by omega) (by omega) h⟩

theorem solution (n : ℕ) (hn : 2 < n)
    (hmod : n % 23 ∈ ({7, 10, 11, 15, 17, 19, 20, 21, 22} : Finset ℕ)) : IsErdosStraus n := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod

  rcases hmod with h | h | h | h | h | h | h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = 23*k + 7 := ⟨n / 23, by omega⟩
    rcases lt_or_ge k 1 with hk | hk
    · interval_cases k
      · exact witness _ 2 15 210 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact witness _ (2 + 6*k) (42 + 138*k) (21 + 132*k + 207*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 23*k + 10 := ⟨n / 23, by omega⟩
    rcases lt_or_ge k 2 with hk | hk
    · interval_cases k
      · exact witness _ 3 16 240 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 9 100 9900 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact witness _ (3 + 6*k) (60 + 138*k) (20 + 86*k + 92*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 23*k + 11 := ⟨n / 23, by omega⟩
    rcases lt_or_ge k 1 with hk | hk
    · interval_cases k
      · exact witness _ 3 34 1122 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact witness _ (3 + 6*k) (66 + 138*k) (66 + 270*k + 276*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 23*k + 15 := ⟨n / 23, by omega⟩
    exact witness _ (4 + 6*k) (90 + 138*k) (180 + 546*k + 414*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 23*k + 17 := ⟨n / 23, by omega⟩
    rcases lt_or_ge k 6 with hk | hk
    · interval_cases k
      · exact witness _ 5 30 510 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 11 111 12210 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 16 1009 1017072 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 22 947 895862 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 28 1018 1553468 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 34 1123 1260006 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact witness _ (6 + 6*k) (102 + 138*k) (17 + 40*k + 23*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 23*k + 19 := ⟨n / 23, by omega⟩
    exact witness _ (5 + 6*k) (114 + 138*k) (570 + 1374*k + 828*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 23*k + 20 := ⟨n / 23, by omega⟩
    rcases lt_or_ge k 3 with hk | hk
    · interval_cases k
      · exact witness _ 6 31 930 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 11 474 224202 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 17 562 315282 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact witness _ (6 + 6*k) (120 + 138*k) (40 + 86*k + 46*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 23*k + 21 := ⟨n / 23, by omega⟩
    rcases lt_or_ge k 2 with hk | hk
    · interval_cases k
      · exact witness _ 6 43 1806 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 12 133 17556 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact witness _ (6 + 6*k) (126 + 138*k) (63 + 132*k + 69*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 23*k + 22 := ⟨n / 23, by omega⟩
    rcases lt_or_ge k 1 with hk | hk
    · interval_cases k
      · exact witness _ 6 67 4422 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact witness _ (6 + 6*k) (132 + 138*k) (132 + 270*k + 138*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
