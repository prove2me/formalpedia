-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB111_uniform_cell_step_sum_eq_floor_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T23:47:32.605283+00:00
-- url     : https://prove2.me/submissions/dbcefc43-7910-438b-a33a-c4d6aa34dd65

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bva20_uniform_step_full_floor_mask_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) (m : ℕ)
    (c : ℕ → ℝ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    let Δ : ℝ := T / ((m : ℝ) + 1)
    (Finset.range (m + 1)).sum (fun i =>
      if ((i : ℝ) * Δ ≤ t ∧
        t < (((i + 1 : ℕ) : ℝ) * Δ)) then c i else 0) =
    c ⌊t / Δ⌋₊ := by
  intro Δ
  let T0 : ℝ := T * ((m : ℝ) + 2) / ((m : ℝ) + 1)
  let u : ℕ → ℝ := fun i => T0 * (i : ℝ) / ((m : ℝ) + 2)
  have hT0 : 0 < T0 := by dsimp [T0]; positivity
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (m : ℝ) + 2 ≠ 0 := by positivity
  have hu (i : ℕ) : u i = (i : ℝ) * Δ := by
    dsimp [u, T0, Δ]
    field_simp
  have hRight :
      T0 * ((m : ℝ) + 1) / ((m : ℝ) + 2) = T := by
    dsimp [T0]
    field_simp
  have hIndex : (t / T0) * ((m : ℝ) + 2) = t / Δ := by
    dsimp [T0, Δ]
    field_simp
  have hBVA :
      (Finset.range (m + 1)).sum (fun i =>
        (Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) =
      if 0 ≤ t ∧
          t < T0 * ((m : ℝ) + 1) / ((m : ℝ) + 2)
      then c ⌊(t / T0) * ((m : ℝ) + 2)⌋₊ else 0 := by
    simpa [u] using
      (avram_bva20_uniform_step_full_floor_mask_identity T0 hT0 m c t)
  calc
    _ = (Finset.range (m + 1)).sum (fun i =>
          (Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hu i, hu (i + 1)]
        simp [Set.indicator_apply, Set.mem_Ico]
    _ = if 0 ≤ t ∧
          t < T0 * ((m : ℝ) + 1) / ((m : ℝ) + 2)
        then c ⌊(t / T0) * ((m : ℝ) + 2)⌋₊ else 0 := hBVA
    _ = c ⌊t / Δ⌋₊ := by
      rw [hRight, hIndex]
      simp [ht.1, ht.2]
