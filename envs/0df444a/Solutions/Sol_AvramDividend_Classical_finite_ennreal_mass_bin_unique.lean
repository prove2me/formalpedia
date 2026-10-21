-- Prove2me | solution 1 for AvramDividend.Classical.finite_ennreal_mass_bin_unique
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T10:23:09.555491+00:00
-- url     : https://prove2.me/submissions/17076cb4-f3bc-4a10-817f-f1597b45560e

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_finite_ennreal_mass_bin_exists

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (m : ℝ≥0∞) (hm : m < ⊤) :
    ∃! n : ℕ, m ≤ (n + 1 : ℝ≥0∞) ∧
      (n = 0 ∨ (n : ℝ≥0∞) < m) := by
  obtain ⟨n, hn⟩ := finite_ennreal_mass_bin_exists m hm
  refine ⟨n, hn, ?_⟩
  intro k hk
  rcases lt_trichotomy n k with hlt | heq | hgt
  · exfalso
    have hknz : k ≠ 0 := by
      intro hk0
      simp [hk0] at hlt
    have hlow : (k : ℝ≥0∞) < m := hk.2.resolve_left hknz
    have hle : (n + 1 : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hlt)
    exact (not_lt_of_ge (le_trans hn.1 hle)) hlow
  · exact heq.symm
  · exfalso
    have hnnz : n ≠ 0 := by
      intro hn0
      simp [hn0] at hgt
    have hlow : (n : ℝ≥0∞) < m := hn.2.resolve_left hnnz
    have hle : (k + 1 : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hgt)
    exact (not_lt_of_ge (le_trans hk.1 hle)) hlow
