-- Prove2me | solution 1 for AvramDividend.Classical.avram_reuse8_nonintegrable_negative_grid_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:35:12.732469+00:00
-- url     : https://prove2.me/submissions/46bdc459-053e-487e-bc14-9c81ec1e76ef

import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (b : ℝ) (F M B E : ℕ → Ω → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFnonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hMI : ∀ n, Integrable (M n) P)
    (hEI : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPhysical : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ b + M n ω + B n ω + max (E n ω) 0) :
    ∀ n, Integrable (F n) P := by
  intro n
  have hUpperI : Integrable
      (fun ω => b + M n ω + max (E n ω) 0) P :=
    ((integrable_const b).add (hMI n)).add (hEI n)
  have hNorm : ∀ᵐ ω ∂P,
      ‖F n ω‖ ≤ b + M n ω + max (E n ω) 0 := by
    filter_upwards [hFnonneg n, hB n, hPhysical n]
      with ω hNonneg hBω hIneq
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    linarith
  exact hUpperI.mono' (hFmeas n).aestronglyMeasurable hNorm
