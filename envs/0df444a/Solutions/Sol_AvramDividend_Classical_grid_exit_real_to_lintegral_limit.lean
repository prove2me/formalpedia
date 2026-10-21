-- Prove2me | solution 1 for AvramDividend.Classical.grid_exit_real_to_lintegral_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:10:41.476323+00:00
-- url     : https://prove2.me/submissions/8d5eaab6-f1a1-47c7-bbb9-1d97e3fec404

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_grid_exit_fatou_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal

/-- Uniform real grid expectations control the liminf-dominated continuous-passage payoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (F : Ω → ENNReal) (f : ℕ → Ω → ℝ)
    (B : ℝ)
    (hMeas : ∀ n : ℕ, Measurable (f n))
    (hInt : ∀ n : ℕ, Integrable (f n) P)
    (hPos : ∀ n : ℕ, ∀ ω, 0 ≤ f n ω)
    (hLimit : ∀ ω : Ω,
      F ω ≤ liminf (fun n => ENNReal.ofReal (f n ω)) atTop)
    (hBound : ∀ n : ℕ, (∫ ω, f n ω ∂P) ≤ B) :
    (∫⁻ ω, F ω ∂P) ≤ ENNReal.ofReal B := by
  have hMeasE : ∀ n : ℕ,
      Measurable (fun ω => ENNReal.ofReal (f n ω)) := by
    intro n
    exact ENNReal.measurable_ofReal.comp (hMeas n)
  have hBoundE : ∀ n : ℕ,
      (∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) ≤ ENNReal.ofReal B := by
    intro n
    have hAe : 0 ≤ᵐ[P] f n :=
      Filter.Eventually.of_forall (hPos n)
    rw [← ofReal_integral_eq_lintegral_ofReal (hInt n) hAe]
    exact ENNReal.ofReal_mono (hBound n)
  exact AvramDividend.Classical.grid_exit_fatou_uniform_bound
    P F (fun n ω => ENNReal.ofReal (f n ω))
    hMeasE hLimit (ENNReal.ofReal B) hBoundE
