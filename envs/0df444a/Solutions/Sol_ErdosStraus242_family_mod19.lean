-- Prove2me | solution 1 for ErdosStraus242.family_mod19
-- status  : ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-11T20:49:02.75052+00:00
-- url     : https://prove2.me/submissions/f5f9252c-7d67-4004-9425-e47ff7439384

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
    (hmod : n % 19 ∈ ({14, 15, 18} : Finset ℕ)) : IsErdosStraus n := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmod

  rcases hmod with h | h | h
  · obtain ⟨k, rfl⟩ : ∃ k, n = 19*k + 14 := ⟨n / 19, by omega⟩
    rcases lt_or_ge k 5 with hk | hk
    · interval_cases k
      · exact witness _ 4 29 812 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 9 100 9900 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 14 183 33306 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 18 1279 1634562 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      · exact witness _ 23 1036 1072260 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact witness _ (5 + 5*k) (70 + 95*k) (14 + 33*k + 19*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 19*k + 15 := ⟨n / 19, by omega⟩
    exact witness _ (4 + 5*k) (75 + 95*k) (300 + 755*k + 475*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
  · obtain ⟨k, rfl⟩ : ∃ k, n = 19*k + 18 := ⟨n / 19, by omega⟩
    rcases lt_or_ge k 1 with hk | hk
    · interval_cases k
      · exact witness _ 5 46 2070 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact witness _ (5 + 5*k) (90 + 95*k) (90 + 185*k + 95*k^2) (by positivity) (by omega) (by omega) (by nlinarith) (by ring)
