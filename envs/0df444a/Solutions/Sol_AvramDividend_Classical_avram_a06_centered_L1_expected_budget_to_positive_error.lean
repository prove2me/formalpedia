-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_centered_L1_expected_budget_to_positive_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:17:45.48819+00:00
-- url     : https://prove2.me/submissions/36c395ec-c18b-4453-9d45-51b031667c0c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped Topology
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ) (K : ℝ)
    (hY : ∀ n, Integrable (Y n) P)
    (hMean : Tendsto (fun n => max ((∫ ω, Y n ω ∂P) - K) 0)
      atTop (𝓝 (0 : ℝ))) :
    ∃ M Err : ℕ → Ω → ℝ,
      (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, AEStronglyMeasurable
        (fun ω => max (Y n ω - (K + M n ω)) 0) P) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P)
        atTop (𝓝 (0 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂P, Y n ω ≤ K + M n ω + max (Err n ω) 0)  := by
  let m : ℕ → ℝ := fun n => ∫ ω, Y n ω ∂P
  let M : ℕ → Ω → ℝ := fun n ω => Y n ω - m n
  let Err : ℕ → Ω → ℝ := fun n _ => max (m n - K) 0
  refine ⟨M, Err, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    constructor
    · exact (hY n).sub (integrable_const _)
    · simp [M, m, integral_sub (hY n) (integrable_const _),
        integral_const, Measure.real, measure_univ, smul_eq_mul]
  · intro n
    have hEq :
        (fun ω => max (Y n ω - (K + M n ω)) 0) =
          (fun _ : Ω => max (m n - K) 0) := by
      funext ω
      have hAlgebra : Y n ω - (K + (Y n ω - m n)) =
          m n - K := by ring
      simp only [M, hAlgebra]
    rw [hEq]
    exact (integrable_const (max (m n - K) 0)).aestronglyMeasurable
  · intro n
    change Integrable
      (fun _ : Ω => max (max (m n - K) 0) 0) P
    exact integrable_const _
  · have hEq (n : ℕ) :
        (∫ ω, max (Err n ω) 0 ∂P) =
          max (m n - K) 0 := by
      have hm : max (max (m n - K) 0) 0 =
          max (m n - K) 0 := max_eq_left (le_max_right _ _)
      simpa [Err, hm, integral_const]
    simp_rw [hEq]
    simpa only [m] using hMean
  · intro n
    filter_upwards [] with ω
    have hNonneg : m n - K ≤ max (m n - K) 0 :=
      le_max_left _ _
    have hId : max (max (m n - K) 0) 0 =
        max (m n - K) 0 := max_eq_left (le_max_right _ _)
    dsimp only [Err, M]
    rw [hId]
    linarith
