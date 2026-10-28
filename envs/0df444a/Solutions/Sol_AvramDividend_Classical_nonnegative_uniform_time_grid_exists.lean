-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_uniform_time_grid_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:52:25.38483+00:00
-- url     : https://prove2.me/submissions/02570ae8-c443-45c2-9588-734639723a0b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal

/-- Equal-duration NNReal grid endpoints from zero to a fixed horizon. -/
theorem solution
    (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    ∃ (ts : ℕ → ℝ≥0) (δ : ℝ≥0),
      ts 0 = 0 ∧ ts N = T ∧
      (∀ k : ℕ, k < N → ts k ≤ ts (k + 1)) ∧
      (∀ k : ℕ, k < N → ts (k + 1) ≤ T) ∧
      (∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) ∧
      (N : ℝ≥0) * δ = T := by
  let δ : ℝ≥0 := T / (N : ℝ≥0)
  let ts : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * δ
  have hNreal : (N : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hTotal : (N : ℝ≥0) * δ = T := by
    dsimp [δ]
    field_simp [hNreal]
  have hSucc (k : ℕ) : ts (k + 1) = ts k + δ := by
    dsimp [ts]
    push_cast
    ring
  have hZero : ts 0 = 0 := by simp [ts]
  have hFinal : ts N = T := by
    simpa only [ts] using hTotal
  refine ⟨ts, δ, hZero, hFinal, ?_, ?_, ?_, hTotal⟩
  · intro k hk
    rw [hSucc k]
    exact le_add_of_nonneg_right (zero_le : (0 : ℝ≥0) ≤ δ)
  · intro k hk
    calc
      ts (k + 1) ≤ ts N := by
        dsimp [ts]
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast (Nat.succ_le_iff.mpr hk)
        · exact (zero_le : (0 : ℝ≥0) ≤ δ)
      _ = T := hFinal
  · intro k hk
    rw [hSucc k]
    exact add_tsub_cancel_left (ts k) δ
