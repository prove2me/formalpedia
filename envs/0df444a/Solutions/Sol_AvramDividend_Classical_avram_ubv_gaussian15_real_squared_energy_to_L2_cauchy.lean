-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian15_real_squared_energy_to_L2_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:13:20.166503+00:00
-- url     : https://prove2.me/submissions/d9ee4e1e-276b-46a9-aab4-5363b56682d8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Vanishing real squared L² energy gives the precise eLpNorm Cauchy
condition used to construct the terminal stochastic integral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Q : ℕ → Ω → ℝ)
    (hPair : ∀ n m, MemLp (Q n - Q m) 2 P)
    (hEnergy : Tendsto (fun nm : ℕ × ℕ =>
      ∫ ω, (Q nm.1 ω - Q nm.2 ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (Q nm.1 - Q nm.2) 2 P) atTop (𝓝 0) := by
  have heq (n m : ℕ) :
      eLpNorm (Q n - Q m) 2 P =
        ENNReal.ofReal (Real.sqrt (∫ ω, (Q n ω - Q m ω) ^ 2 ∂P)) := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm
      (by norm_num) (by norm_num) (hPair n m)]
    simp [Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs]
  have hsqrt : Tendsto (fun nm : ℕ × ℕ =>
      Real.sqrt (∫ ω, (Q nm.1 ω - Q nm.2 ω) ^ 2 ∂P))
      atTop (𝓝 0) := by
    have hcomp := (Real.continuous_sqrt.tendsto 0).comp hEnergy
    change Tendsto (fun nm : ℕ × ℕ =>
      Real.sqrt (∫ ω, (Q nm.1 ω - Q nm.2 ω) ^ 2 ∂P))
      atTop (𝓝 (Real.sqrt 0)) at hcomp
    simpa only [Real.sqrt_zero] using hcomp
  have hENN : Tendsto (fun nm : ℕ × ℕ =>
      ENNReal.ofReal (Real.sqrt
        (∫ ω, (Q nm.1 ω - Q nm.2 ω) ^ 2 ∂P))) atTop (𝓝 0) := by
    have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp hsqrt
    change Tendsto (fun nm : ℕ × ℕ =>
      ENNReal.ofReal (Real.sqrt
        (∫ ω, (Q nm.1 ω - Q nm.2 ω) ^ 2 ∂P)))
      atTop (𝓝 (ENNReal.ofReal 0)) at hcomp
    simpa only [ENNReal.ofReal_zero] using hcomp
  simpa only [heq] using hENN
