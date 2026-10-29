-- Prove2me | solution 2 for AvramDividend.Classical.avram_ws01e_bt_new_bv_mesh_grid_calibration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:32:18.617206+00:00
-- url     : https://prove2.me/submissions/91945c72-4ef3-446a-8f49-fc5e99006935

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-- A uniform nonnegative-time mesh has the exact width and exponential
calibration needed by the genuine BV Lévy surviving-deficit bounds. -/
theorem solution
    (d : ℝ) (hd : 0 < d)
    (T : ℝ≥0) (hT : 0 < T)
    (N : ℕ) (hN : 0 < N)
    (hLarge : 2 * d * (T : ℝ) ≤ (N : ℝ)) :
    (let δ : ℝ≥0 := T / (N : ℝ≥0)
     let ts : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * δ
     let a : ℝ := d * (δ : ℝ)
     0 < a ∧
     ts N = T ∧
     (∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) ∧
     (∀ k : ℕ, k < N → ts (k + 1) ≤ T) ∧
     1 ≤ 1 / (2 * a) ∧
     (δ : ℝ) * (1 / (2 * a)) = 1 / (2 * d) ∧
     4 * a * (N : ℝ) = 4 * d * (T : ℝ)) := by
  classical
  let δ : ℝ≥0 := T / (N : ℝ≥0)
  let ts : ℕ → ℝ≥0 := fun k => (k : ℝ≥0) * δ
  let a : ℝ := d * (δ : ℝ)
  change 0 < a ∧ ts N = T ∧
    (∀ k : ℕ, k < N → ts (k + 1) - ts k = δ) ∧
    (∀ k : ℕ, k < N → ts (k + 1) ≤ T) ∧
    1 ≤ 1 / (2 * a) ∧
    (δ : ℝ) * (1 / (2 * a)) = 1 / (2 * d) ∧
    4 * a * (N : ℝ) = 4 * d * (T : ℝ)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNnr : (0 : ℝ≥0) < N := by exact_mod_cast hN
  have hδ : 0 < δ := div_pos hT hNnr
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have ha : 0 < a := mul_pos hd hδr
  have htsN : ts N = T := by
    dsimp [ts, δ]
    field_simp [ne_of_gt hNnr]
  have htsStep (k : ℕ) : ts (k + 1) = ts k + δ := by
    dsimp [ts]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have htsDiff (k : ℕ) (_ : k < N) :
      ts (k + 1) - ts k = δ := by
    rw [htsStep]
    exact add_tsub_cancel_left (ts k) δ
  have htsWithin (k : ℕ) (hk : k < N) :
      ts (k + 1) ≤ T := by
    rw [← htsN]
    dsimp [ts]
    exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.succ_le_of_lt hk) bot_le
  have hδEq : (δ : ℝ) = (T : ℝ) / (N : ℝ) := by
    simp [δ]
  have hsmall_mul : 2 * a * (N : ℝ) ≤ (N : ℝ) := by
    calc
      2 * a * (N : ℝ) = 2 * d * (T : ℝ) := by
        dsimp [a]
        rw [hδEq]
        field_simp [ne_of_gt hNr]
      _ ≤ (N : ℝ) := hLarge
  have hsmall : 2 * a ≤ 1 := by
    by_contra hh
    have hgt : 1 < 2 * a := lt_of_not_ge hh
    have hpos : 0 < (2 * a - 1) * (N : ℝ) :=
      mul_pos (sub_pos.mpr hgt) hNr
    nlinarith [hsmall_mul]
  have hRate : 1 ≤ 1 / (2 * a) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * a)).mpr
    nlinarith [hsmall]
  have hProduct : (δ : ℝ) * (1 / (2 * a)) =
      1 / (2 * d) := by
    dsimp [a]
    field_simp [ne_of_gt hd, ne_of_gt hδr]
  have hPref : 4 * a * (N : ℝ) = 4 * d * (T : ℝ) := by
    dsimp [a]
    rw [hδEq]
    field_simp [ne_of_gt hNr]
  exact ⟨ha, htsN, htsDiff, htsWithin, hRate, hProduct, hPref⟩
