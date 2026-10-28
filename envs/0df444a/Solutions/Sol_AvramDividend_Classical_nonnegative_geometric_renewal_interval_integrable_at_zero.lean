-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_geometric_renewal_interval_integrable_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:16:10.143694+00:00
-- url     : https://prove2.me/submissions/8bb066dd-b613-4c81-acda-2041249a1d2b

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A geometrically bounded nonnegative renewal series is integrable from zero. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hpoint : ∀ x : ℝ, Summable (fun n : ℕ => F n x))
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) ≤ ρ ^ (n + 1)) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y) volume 0 x := by
  have hgeom : Summable (fun n : ℕ => ρ ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hρnonneg hρlt).mul_left ρ
  have hmasssum :
      Summable (fun n : ℕ =>
        ∫ x in Ioi (0 : ℝ), F n x ∂volume) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact integral_nonneg (hpos n)
    · exact hmass
    · exact hgeom
  have hint : Integrable (fun y : ℝ => ∑' n : ℕ, F n y)
      (volume.restrict (Ioi (0 : ℝ))) :=
    AvramDividend.Classical.nonnegative_integrable_tsum_of_summable_integrals
      (volume.restrict (Ioi (0 : ℝ))) F hFi hpos hpoint hmasssum
  intro x hx
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hx)).2
  exact IntegrableOn.mono_set hint (by
    intro y hy
    exact hy.1)
