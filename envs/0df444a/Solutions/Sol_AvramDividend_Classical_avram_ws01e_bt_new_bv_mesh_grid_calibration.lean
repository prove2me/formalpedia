-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bt_new_bv_mesh_grid_calibration
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T23:31:44.2083+00:00
-- url     : https://prove2.me/submissions/f023c381-a288-488a-8b61-e53dff017277

import Mathlib
open scoped NNReal

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
  intro δ ts a
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast hN.ne'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hδr : (δ : ℝ) = (T : ℝ) / N := by simp [δ]
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hδpos : (0 : ℝ) < δ := by rw [hδr]; positivity
  have ha : a = d * T / N := by simp only [a]; rw [hδr]; ring
  have hapos : 0 < a := by rw [ha]; positivity
  have htsN : ts N = T := by simp only [ts, δ]; field_simp
  refine ⟨hapos, htsN, ?_, ?_, ?_, ?_, ?_⟩
  · intro k _; simp only [ts]; push_cast; rw [add_mul, one_mul, add_tsub_cancel_left]
  · intro k hk
    rw [← htsN]; simp only [ts]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) zero_le
  · rw [le_div_iff₀ (by positivity), one_mul, ha, mul_div_assoc', div_le_one hNr]; linarith
  · simp only [a]; field_simp
  · rw [ha]; field_simp
