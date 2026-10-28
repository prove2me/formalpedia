-- Prove2me | solution 1 for AvramDividend.Classical.levy_capped_upper_grid_exp_expectation_of_ae_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T09:28:09.344958+00:00
-- url     : https://prove2.me/submissions/85ff13b5-66b3-4df3-b31e-4c3c1cea2e5d

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_upper_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_levy_capped_upcrossing_compensated_exp_second_moment_bound
import Theorems.Thm_AvramDividend_Classical_levy_capped_upcrossing_compensated_exp_square_integrable
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

/-- Uniform L² control transfers stopped exponential grid limits to expectations. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℕ → ℝ≥0)
    (hc : ∀ n, Monotone (clock n)) (hc0 : ∀ n, clock n 0 = 0)
    (H : ℕ → Filtration ℕ mΩ)
    (hH : ∀ n k, H n k = 𝓕 (clock n k))
    (θ : ℝ) (hθ : 0 ≤ θ) (z : ℝ) (m : ℕ → ℕ)
    (N : ℝ≥0) (hNm : ∀ n, clock n (m n) ≤ N)
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n =>
      let K := hittingBtwn (fun k η => X.X (clock n k) η) (Ioi z) 0 (m n) ω
      Real.exp (θ * X.X (clock n K) ω - (clock n K : ℝ) * X.ψ θ))
      atTop (𝓝 (Z ω))) :
    Integrable Z P ∧ Tendsto (fun n => ∫ ω,
      let K := hittingBtwn (fun k η => X.X (clock n k) η) (Ioi z) 0 (m n) ω
      Real.exp (θ * X.X (clock n K) ω - (clock n K : ℝ) * X.ψ θ) ∂P)
      atTop (𝓝 (∫ ω, Z ω ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : ℕ → Ω → ℝ := fun n ω =>
    let K := hittingBtwn (fun k η => X.X (clock n k) η) (Ioi z) 0 (m n) ω
    Real.exp (θ * X.X (clock n K) ω - (clock n K : ℝ) * X.ψ θ)
  have hYm : ∀ n, AEStronglyMeasurable (Y n) P := by
    intro n
    let Kn : Ω → ℕ := fun ω =>
      hittingBtwn (fun k η => X.X (clock n k) η) (Ioi z) 0 (m n) ω
    obtain ⟨hZ, hT⟩ := levy_upper_grid_stopped_reserve_time_measurable
      X (clock n) (H n) (hH n) z (m n) Kn (fun _ => rfl)
    have hm : Measurable (fun ω => Real.exp
        (θ * X.X (clock n (Kn ω)) ω -
          (clock n (Kn ω) : ℝ) * X.ψ θ)) :=
      Real.measurable_exp.comp
        ((measurable_const.mul hZ).sub (hT.mul measurable_const))
    simpa only [Y, Kn] using hm.aestronglyMeasurable
  have hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω := by
    intro n
    exact Filter.Eventually.of_forall (fun ω => Real.exp_nonneg _)
  let C : ℝ := Real.exp ((N : ℝ) * max (X.ψ (2 * θ) - 2 * X.ψ θ) 0)
  have hC : 0 ≤ C := Real.exp_nonneg _
  have hY2 : ∀ n, Integrable (fun ω => (Y n ω)^2) P ∧
      ∫ ω, (Y n ω)^2 ∂P ≤ C := by
    intro n
    have hi : Integrable (fun ω => (Y n ω)^2) P := by
      simpa only [Y] using
        (levy_capped_upcrossing_compensated_exp_square_integrable
          X (clock n) (hc n) (H n) (hH n) θ hθ z (m n))
    have hb : (∫ ω, (Y n ω)^2 ∂P) ≤
        Real.exp ((clock n (m n) : ℝ) *
          max (X.ψ (2 * θ) - 2 * X.ψ θ) 0) := by
      simpa only [Y] using
        (levy_capped_upcrossing_compensated_exp_second_moment_bound
          X (clock n) (hc n) (hc0 n) (H n) (hH n) θ hθ z (m n))
    have ht : (clock n (m n) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hNm n
    have hh : 0 ≤ max (X.ψ (2 * θ) - 2 * X.ψ θ) 0 :=
      le_max_right _ _
    exact ⟨hi, hb.trans (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right ht hh))⟩
  exact nonnegative_integral_tendsto_of_uniform_second_moment
    Y Z hYm hY0 hZm hconv C hC hY2
