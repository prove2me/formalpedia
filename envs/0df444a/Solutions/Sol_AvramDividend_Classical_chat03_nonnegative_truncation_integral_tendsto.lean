-- Prove2me | solution 1 for AvramDividend.Classical.chat03_nonnegative_truncation_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:49:03.189992+00:00
-- url     : https://prove2.me/submissions/edbbccb2-73c4-4892-a2a6-3be3f373a18d

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.OrderClosed

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped ENNReal

/-!
Dominated convergence for uniformly bounded nonnegative truncations.
This is the finite-cutoff component of convergence under L2 bounds.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω))) :
    Tendsto (fun n => ∫ ω, min (Y n ω) R ∂P) atTop
      (𝓝 (∫ ω, min (Z ω) R ∂P)) := by
  have hc : Continuous (fun y : ℝ => min y R) :=
    continuous_id.min continuous_const
  have hmeas (n : ℕ) :
      AEStronglyMeasurable (fun ω => min (Y n ω) R) P :=
    hc.comp_aestronglyMeasurable (hYm n)
  have hbound : ∀ n, ∀ᵐ ω ∂P, ‖min (Y n ω) R‖ ≤ R := by
    intro n
    filter_upwards [hY0 n] with ω hy
    have hmin : 0 ≤ min (Y n ω) R := le_min hy hR
    simpa [Real.norm_eq_abs, abs_of_nonneg hmin] using
      (min_le_right (Y n ω) R)
  have hlim :
      ∀ᵐ ω ∂P, Tendsto (fun n => min (Y n ω) R) atTop
        (𝓝 (min (Z ω) R)) := by
    filter_upwards [hconv] with ω hω
    exact (hc.tendsto (Z ω)).comp hω
  exact tendsto_integral_of_dominated_convergence
    (fun _ : Ω => R) hmeas (integrable_const R) hbound hlim
