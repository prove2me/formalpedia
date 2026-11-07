-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_centered_gap_positive_error_aggregation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:56:56.868138+00:00
-- url     : https://prove2.me/submissions/fdf63c3e-9558-45fe-bcf9-a0f25ceb1a26

import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- A vanishing positive expected signed gap produces a mean-zero residual and
    a vanishing positive-error source without changing either random payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F B : ℕ → Ω → ℝ) (a : ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hBI : ∀ n, Integrable (B n) P)
    (hgap : Tendsto
      (fun n => max ((∫ ω, F n ω ∂P) - a - (∫ ω, B n ω ∂P)) 0)
      atTop (𝓝 0)) :
    ∃ M Err : ℕ → Ω → ℝ,
      (∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      Tendsto (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0) ∧
      (∀ n ω, F n ω ≤ a + (M n ω + B n ω) + max (Err n ω) 0) := by
  let z : ℕ → ℝ := fun n =>
    (∫ ω, F n ω ∂P) - a - (∫ ω, B n ω ∂P)
  let M : ℕ → Ω → ℝ := fun n ω => F n ω - a - B n ω - z n
  let Err : ℕ → Ω → ℝ := fun n _ => z n
  refine ⟨M, Err, ?_, ?_, ?_, ?_⟩
  · intro n
    constructor
    · exact (((hFI n).sub (integrable_const a)).sub (hBI n)).sub
        (integrable_const (z n))
    · have hfa : Integrable (fun ω => F n ω - a) P :=
        (hFI n).sub (integrable_const a)
      have hfab : Integrable (fun ω => F n ω - a - B n ω) P :=
        hfa.sub (hBI n)
      calc
        (∫ ω, M n ω ∂P) =
            (∫ ω, F n ω ∂P) - a - (∫ ω, B n ω ∂P) - z n := by
              dsimp [M]
              rw [integral_sub hfab (integrable_const (z n))]
              rw [integral_sub hfa (hBI n)]
              rw [integral_sub (hFI n) (integrable_const a)]
              simp
        _ = 0 := by dsimp [z]; ring
  · intro n
    change Integrable (fun _ : Ω => max (z n) 0) P
    exact integrable_const _
  · simpa [Err, z] using hgap
  · intro n ω
    dsimp [M, Err]
    have hz : z n ≤ max (z n) 0 := le_max_left _ _
    nlinarith
