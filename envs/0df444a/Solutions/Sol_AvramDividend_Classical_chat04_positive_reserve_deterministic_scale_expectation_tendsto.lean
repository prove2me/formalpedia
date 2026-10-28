-- Prove2me | solution 1 for AvramDividend.Classical.chat04_positive_reserve_deterministic_scale_expectation_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T14:16:57.493993+00:00
-- url     : https://prove2.me/submissions/7615da0c-cdd5-4cf5-87a2-55916d31a8e6

import Theorems.Thm_AvramDividend_Classical_chat04_deterministic_horizon_scale_l2_uniform_bound
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_discounted_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

/-- Expected discounted scale rewards approach the initial scale for every
bounded deterministic time sequence converging to zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x)
    (N : ℝ≥0) (t : ℕ → ℝ≥0) (htN : ∀ n, t n ≤ N)
    (ht0 : Filter.Tendsto t Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n => ∫ ω, Real.exp (-(q * (t n : ℝ))) *
        W (x + X.X (t n) ω) ∂P)
      Filter.atTop (𝓝 (W x)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) ω)
  have hWmeas : Measurable W :=
    chat03_scale_function_borel_measurable X q W hW
  have hYm : ∀ n, AEStronglyMeasurable (Y n) P := by
    intro n
    have hReserve : Measurable (X.X (t n)) :=
      (X.adapted (t n)).mono (𝓕.le (t n)) le_rfl
    have hScale : Measurable (fun ω =>
        W (x + X.X (t n) ω)) :=
      hWmeas.comp (measurable_const.add hReserve)
    have hDiscount : Measurable (fun _ : Ω =>
        Real.exp (-(q * (t n : ℝ)))) := measurable_const
    have hProduct : Measurable (fun ω : Ω =>
        Real.exp (-(q * (t n : ℝ))) * W (x + X.X (t n) ω)) := by
      convert (hDiscount.mul hScale) using 1
      funext ω
      simp only [Pi.mul_apply]
    exact hProduct.aestronglyMeasurable
  have hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω := by
    intro n
    apply Filter.Eventually.of_forall
    intro ω
    dsimp [Y]
    apply mul_nonneg (Real.exp_nonneg _)
    by_cases hy : 0 ≤ x + X.X (t n) ω
    · exact hW.2.1 _ hy
    · simp [hW.1 _ (lt_of_not_ge hy)]
  have hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n => Y n ω) atTop (𝓝 (W x)) := by
    apply Filter.Eventually.of_forall
    intro ω
    exact (chat04_positive_reserve_discounted_scale_tendsto_initial
      X q W hW x hx ω).comp ht0
  let C : ℝ := ((X.ψ θ - q)⁻¹)^2 *
    Real.exp (2 * θ * (x + 1) + (N : ℝ) * max (X.ψ (2 * θ)) 0)
  have hC : 0 ≤ C :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  have hY2 : ∀ n, Integrable (fun ω => (Y n ω)^2) P ∧
      ∫ ω, (Y n ω)^2 ∂P ≤ C := by
    intro n
    simpa [Y, C] using
      (chat04_deterministic_horizon_scale_l2_uniform_bound
        X q hq W hW θ x hθ hψ N (t n) (htN n))
  have hmain := (nonnegative_integral_tendsto_of_uniform_second_moment
    Y (fun _ => W x) hYm hY0
    measurable_const.aestronglyMeasurable hconv C hC hY2).2
  simpa [Y] using hmain