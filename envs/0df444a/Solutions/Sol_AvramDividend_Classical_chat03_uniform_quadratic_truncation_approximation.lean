-- Prove2me | solution 1 for AvramDividend.Classical.chat03_uniform_quadratic_truncation_approximation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:25:59.177404+00:00
-- url     : https://prove2.me/submissions/254d2ea8-abfb-4686-a819-16558baeec56

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_truncation_integral_error_bound
import Theorems.Thm_AvramDividend_Classical_chat03_positive_cutoff_makes_quadratic_error_small

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical

/-!
A common quadratic-moment bound supplies arbitrarily accurate real
integral truncations uniformly over every member of a sequence.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω)
    (hZm : AEStronglyMeasurable Z P)
    (hZ0 : ∀ᵐ ω ∂P, 0 ≤ Z ω)
    (C : ℝ) (hC : 0 ≤ C)
    (hY2 : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P ∧
      ∫ ω, (Y n ω) ^ 2 ∂P ≤ C)
    (hZ2 : Integrable (fun ω => (Z ω) ^ 2) P ∧
      ∫ ω, (Z ω) ^ 2 ∂P ≤ C) :
    ∀ ε > 0, ∃ R > 0,
      (∀ n, dist (∫ ω, Y n ω ∂P)
        (∫ ω, min (Y n ω) R ∂P) ≤ ε) ∧
      dist (∫ ω, min (Z ω) R ∂P) (∫ ω, Z ω ∂P) ≤ ε := by
  intro ε hε
  obtain ⟨R, hR, hsmall⟩ :=
    chat03_positive_cutoff_makes_quadratic_error_small C ε hC hε
  refine ⟨R, hR, ?_, ?_⟩
  · intro n
    have he := chat03_nonnegative_truncation_integral_error_bound
      (Y n) R C hR (hYm n) (hY0 n) (hY2 n)
    rw [Real.dist_eq, abs_of_nonneg he.1]
    exact he.2.trans hsmall
  · have he := chat03_nonnegative_truncation_integral_error_bound
      Z R C hR hZm hZ0 hZ2
    rw [dist_comm, Real.dist_eq, abs_of_nonneg he.1]
    exact he.2.trans hsmall
