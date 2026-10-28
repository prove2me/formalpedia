-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_fixed_horizon_strict_reversal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T01:08:25.974567+00:00
-- url     : https://prove2.me/submissions/7be45c28-19ef-4f9a-9ba9-905381c2cd6a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finite_dyadic_grid_refines
import Theorems.Thm_AvramDividend_Classical_levy_equal_mesh_path_drawdown_minimum_strict_threshold_ws01e_b
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (a : ℝ) :
    P {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < a} =
    P {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < a} := by
  -- grid events
  let G : ℕ → (ℝ≥0 → ℝ) → Prop := fun n f =>
    ∃ k : Fin ((2 : ℕ) ^ n + 1), f (((k.val : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) < a
  have hmono : ∀ f : ℝ≥0 → ℝ, Monotone (fun n => G n f) := by
    intro f
    refine monotone_nat_of_le_succ (fun n => ?_)
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := avram_ws01e_b_finite_dyadic_grid_refines T n k
    exact ⟨j, by rw [hj]; exact hk⟩
  have hA : {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < a} =
      ⋃ n, {ω | G n (fun s => X.X T ω - X.X s ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    refine avram_ws01e_b_right_continuous_strict_dyadic_grid_event
      (fun s => X.X T ω - X.X s ω) T hT (fun s => ?_) a
    exact continuousWithinAt_const.sub (X.rightCont ω s)
  have hB : {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < a} =
      ⋃ n, {ω | G n (fun s => X.X s ω - X.X 0 ω)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    refine avram_ws01e_b_right_continuous_strict_dyadic_grid_event
      (fun s => X.X s ω - X.X 0 ω) T hT (fun s => ?_) a
    exact (X.rightCont ω s).sub continuousWithinAt_const
  have hgrid : ∀ n (k : ℕ), ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T = (k : ℝ≥0) * (T / 2 ^ n) := by
    intro n k; rw [div_mul_eq_mul_div, mul_div_assoc]
  have heq : ∀ n, P {ω | G n (fun s => X.X T ω - X.X s ω)} =
      P {ω | G n (fun s => X.X s ω - X.X 0 ω)} := by
    intro n
    have h := levy_equal_mesh_path_drawdown_minimum_strict_threshold_ws01e_b X (T / 2 ^ n) (2 ^ n) a
    have hT' : (((2 ^ n : ℕ) : ℝ≥0)) * (T / 2 ^ n) = T := by
      push_cast; rw [mul_div_cancel₀]; positivity
    simp only [G, hgrid]
    rw [hT'] at h
    convert h using 3
  have m1 : Monotone (fun n => {ω | G n (fun s => X.X T ω - X.X s ω)}) :=
    fun m n hmn ω h => hmono (fun s => X.X T ω - X.X s ω) hmn h
  have m2 : Monotone (fun n => {ω | G n (fun s => X.X s ω - X.X 0 ω)}) :=
    fun m n hmn ω h => hmono (fun s => X.X s ω - X.X 0 ω) hmn h
  rw [hA, hB, m1.measure_iUnion, m2.measure_iUnion]
  simp_rw [heq]
