-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_finite_capped_grid_right_clock_ws01c
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:20:30.995108+00:00
-- url     : https://prove2.me/submissions/214fcf7b-ebf8-4b59-afe2-978415cb0de8

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_grid_capped_NNReal_stopping_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_observation_times_within_mesh_horizon_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_actual_finite_grid_clock_prefix_cap_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_capped_lower_grid_clock_tendsto_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_raw_strict_lower_clock_le_grid_cap_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_capped_grid_ENNReal_toNNReal_right_limit_ws01c

open Filter MeasureTheory Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (lower : ℝ) (T : ℝ≥0) (mesh : ℕ → ℝ≥0) (M : ℕ → ℕ)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0)))
    (hCover : ∀ n, T ≤ (M n : ℝ≥0) * mesh n) :
    let grid : ℕ → Ω → ℝ≥0 := fun n ω =>
      bv_finite_grid_below_NNReal_ws01c X.X lower
        ((M n : ℝ≥0) * mesh n)
        ((List.range (M n + 1)).map
          (fun k : ℕ => (k : ℝ≥0) * mesh n)) ω ⊓ T
    (∀ n s, MeasurableSet[ℱ s] {ω : Ω | grid n ω ≤ s}) ∧
    (∀ ω, Tendsto (fun n => grid n ω) atTop
      (𝓝 ((twoSidedExitDownTime X lower ω ⊓
        (T : ℝ≥0∞)).toNNReal))) ∧
    (∀ ω n, (twoSidedExitDownTime X lower ω ⊓
        (T : ℝ≥0∞)).toNNReal ≤ grid n ω) := by
  intro grid
  have hL : ∀ n, ∀ t ∈ (List.range (M n + 1)).map (fun k : ℕ => (k : ℝ≥0) * mesh n),
      t ≤ (M n : ℝ≥0) * mesh n := fun n =>
    AvramDividend.Classical.bv_observation_times_within_mesh_horizon_ws01c (mesh n) (M n)
  have hY : ∀ t, Measurable[ℱ t] (X.X t) := fun t => X.adapted t
  have hEq : ∀ n ω, (grid n ω : ℝ≥0∞) =
      (⨅ (k : ℕ) (_ : k ≤ M n),
        if X.X ((k : ℝ≥0) * mesh n) ω < lower then
          (((k : ℝ≥0) * mesh n) : ℝ≥0∞) else ⊤) ⊓ (T : ℝ≥0∞) := by
    intro n ω
    rw [← AvramDividend.Classical.bv_actual_finite_grid_clock_prefix_cap_ws01c X.X ω lower
      (mesh n) T ((M n : ℝ≥0) * mesh n) (M n) (hCover n)]
    simp only [grid, ENNReal.coe_min]
  have hR := AvramDividend.Classical.bv_capped_grid_ENNReal_toNNReal_right_limit_ws01c grid
    (twoSidedExitDownTime X lower) T
    (fun ω => by
      simp_rw [hEq]
      exact AvramDividend.Classical.bv_finite_capped_lower_grid_clock_tendsto_ws01c X ω lower T
        mesh M hpos hzero hCover)
    (fun ω n => by
      rw [hEq]
      exact AvramDividend.Classical.bv_raw_strict_lower_clock_le_grid_cap_ws01c
        (fun t => X.X t ω) lower (mesh n) T (M n))
  refine ⟨?_, hR.1, hR.2⟩
  intro n s
  have hst := AvramDividend.Classical.bv_finite_grid_capped_NNReal_stopping_ws01c ℱ X.X lower
    ((M n : ℝ≥0) * mesh n) T _ (hL n) hY
  have := hst.measurableSet_le s
  convert this using 2
  ext ω
  simp only [grid]
  rw [← WithTop.coe_min, WithTop.coe_le_coe]
