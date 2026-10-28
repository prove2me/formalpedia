-- Prove2me | solution 1 for AvramDividend.Classical.esscher_infimum_bounded_laplace_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:36:00.721696+00:00
-- url     : https://prove2.me/submissions/e012cf70-af94-4b6c-8e55-c5f5f1f7e3a5

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter

/-- Bounded convergence for Laplace transforms of nonnegative infimum magnitudes. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsFiniteMeasure Q]
    (Y : ℕ → Ω → ℝ) (Yinf : Ω → ℝ)
    (β : ℝ) (hβ : 0 < β)
    (hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω => Real.exp (-β * Y n ω)) Q)
    (hpos : ∀ n : ℕ, ∀ᵐ ω ∂Q, 0 ≤ Y n ω)
    (hlim : ∀ᵐ ω ∂Q,
      Tendsto (fun n : ℕ => Y n ω) atTop (nhds (Yinf ω))) :
    Tendsto (fun n : ℕ => ∫ ω, Real.exp (-β * Y n ω) ∂Q)
      atTop (nhds (∫ ω, Real.exp (-β * Yinf ω) ∂Q)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ : Ω => (1 : ℝ)) hmeas (integrable_const _) ?_ ?_
  · intro n
    filter_upwards [hpos n] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply (Real.exp_le_one_iff).2
    have hm : 0 ≤ β * Y n ω := mul_nonneg hβ.le hω
    linarith
  · filter_upwards [hlim] with ω hω
    have hscaled :
        Tendsto (fun n : ℕ => (-β) * Y n ω)
          atTop (nhds ((-β) * Yinf ω)) :=
      tendsto_const_nhds.mul hω
    exact (Real.continuous_exp.tendsto _).comp hscaled
