-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_canonical_physical_source_compensated_centering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T22:01:51.961188+00:00
-- url     : https://prove2.me/submissions/a1019f90-adeb-43ed-9dd6-a52889baf505

import Mathlib
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Source Q : ℕ → Ω → ℝ)
    (hSourceI : ∀ j, Integrable (Source j) P)
    (hQI : ∀ j, Integrable (Q j) P) :
    ∃ (bias : ℕ → ℝ) (M : ℕ → Ω → ℝ),
      (∀ j, bias j = ∫ ω, Source j ω - Q j ω ∂P) ∧
      (∀ j ω, Source j ω = M j ω + Q j ω + bias j) ∧
      (∀ j, Integrable (M j) P) ∧
      (∀ j, (∫ ω, M j ω ∂P) = 0) := by
  let bias : ℕ → ℝ := fun j => ∫ ω, Source j ω - Q j ω ∂P
  let M : ℕ → Ω → ℝ := fun j ω =>
    Source j ω - Q j ω - bias j
  refine ⟨bias, M, ?_, ?_, ?_, ?_⟩
  · intro j
    rfl
  · intro j ω
    dsimp [M]
    ring
  · intro j
    exact ((hSourceI j).sub (hQI j)).sub (integrable_const _)
  · intro j
    have hDiff : Integrable (fun ω => Source j ω - Q j ω) P :=
      (hSourceI j).sub (hQI j)
    change (∫ ω, (Source j ω - Q j ω) - bias j ∂P) = 0
    rw [MeasureTheory.integral_sub hDiff (integrable_const _)]
    simp [bias]