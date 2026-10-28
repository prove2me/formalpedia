-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_fixed_terminal_esscher_strict_drawdown_infimum_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T12:54:18.660394+00:00
-- url     : https://prove2.me/submissions/b7b1c9cf-806d-4517-9674-d4b44fe24dad

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_right_continuous_strict_dyadic_grid_event
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_finite_dyadic_grid_refines
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_terminal_esscher_grid_reversal
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_strict_grid_path_probability_of_vector_reversal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (hT : 0 < T)
    (θ a : ℝ) :
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (X.X T ω - X.X 0 ω) - (T : ℝ) * X.ψ θ)))
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧
        X.X T ω - X.X s ω < a}) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
      (Real.exp (θ * (X.X T ω - X.X 0 ω) - (T : ℝ) * X.ψ θ)))
      {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧
        X.X s ω - X.X 0 ω < a}) := by
  let Q : Measure Ω := P.withDensity (fun ω : Ω => ENNReal.ofReal
    (Real.exp (θ * (X.X T ω - X.X 0 ω) - (T : ℝ) * X.ψ θ)))
  let G : ℕ → (ℝ≥0 → ℝ) → Prop := fun n f =>
    ∃ k : Fin ((2 : ℕ) ^ n + 1),
      f (((k.val : ℝ≥0) / (2 : ℝ≥0) ^ n) * T) < a
  have hmono : ∀ f : ℝ≥0 → ℝ, Monotone (fun n => G n f) := by
    intro f; refine monotone_nat_of_le_succ (fun n => ?_)
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := avram_ws01e_b_finite_dyadic_grid_refines T n k
    exact ⟨j, by simpa only [hj] using hk⟩
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
  have hgrid : ∀ n (k : ℕ),
      ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T =
      (k : ℝ≥0) * (T / 2 ^ n) := by
    intro n k; rw [div_mul_eq_mul_div, mul_div_assoc]
  have heq : ∀ n, Q {ω | G n (fun s => X.X T ω - X.X s ω)} =
      Q {ω | G n (fun s => X.X s ω - X.X 0 ω)} := by
    intro n
    have hT' : (((2 ^ n : ℕ) : ℝ≥0)) * (T / 2 ^ n) = T := by
      push_cast
      rw [mul_div_cancel₀]; positivity
    have hReversal : ∀ A : Set (Fin (2 ^ n) → ℝ), MeasurableSet A →
      Q {ω : Ω | (fun i : Fin (2 ^ n) =>
          X.X (((i.rev.val + 1 : ℕ) : ℝ≥0) * (T / 2 ^ n)) ω -
          X.X ((i.rev.val : ℝ≥0) * (T / 2 ^ n)) ω) ∈ A} =
      Q {ω : Ω | (fun i : Fin (2 ^ n) =>
          X.X (((i.val + 1 : ℕ) : ℝ≥0) * (T / 2 ^ n)) ω -
          X.X ((i.val : ℝ≥0) * (T / 2 ^ n)) ω) ∈ A} := by
      intro A hA
      have h := avram_ws01e_b_actual_terminal_esscher_grid_reversal
        X (T / 2 ^ n) (2 ^ n) θ A hA
      simpa only [hT', Q] using h
    have h := avram_ws01e_b_strict_grid_path_probability_of_vector_reversal
      X (T / 2 ^ n) (2 ^ n) Q a hReversal
    simp only [G, hgrid]
    rw [hT'] at h; convert h using 3
  have m1 : Monotone (fun n => {ω | G n (fun s => X.X T ω - X.X s ω)}) :=
    fun m n hmn ω h => hmono (fun s => X.X T ω - X.X s ω) hmn h
  have m2 : Monotone (fun n => {ω | G n (fun s => X.X s ω - X.X 0 ω)}) :=
    fun m n hmn ω h => hmono (fun s => X.X s ω - X.X 0 ω) hmn h
  change Q {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X T ω - X.X s ω < a} =
    Q {ω : Ω | ∃ s : ℝ≥0, s ≤ T ∧ X.X s ω - X.X 0 ω < a}
  rw [hA, hB, m1.measure_iUnion, m2.measure_iUnion]
  simp_rw [heq]
