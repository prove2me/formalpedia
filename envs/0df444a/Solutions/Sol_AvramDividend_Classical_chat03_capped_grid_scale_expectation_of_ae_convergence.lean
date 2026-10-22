-- Prove2me | solution 1 for AvramDividend.Classical.chat03_capped_grid_scale_expectation_of_ae_convergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T11:58:14.596356+00:00
-- url     : https://prove2.me/submissions/ef1bff4d-32d7-4661-9509-803294a601f7

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_reserve_time_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_grid_l2_unconditional
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.Probability.Process.HittingTime

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

/-!
Transfer almost-everywhere convergence of actual finite-grid stopped
q-scale values to expectation convergence using the verified, mesh-uniform
L² bound. Stochastic q-harmonicity is not assumed.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (clock : ℕ → ℕ → ℝ≥0)
    (hc : ∀ n, Monotone (clock n))
    (hc0 : ∀ n, clock n 0 = 0)
    (H : ℕ → Filtration ℕ mΩ)
    (hH : ∀ n k, H n k = 𝓕 (clock n k))
    (lower upper : ℝ) (m : ℕ → ℕ) (K : ℕ → Ω → ℕ)
    (hK : ∀ n ω, K n ω = hittingBtwn
      (fun k ω => max (X.X (clock n k) ω - upper)
        (lower - X.X (clock n k) ω)) (Set.Ioi (0 : ℝ)) 0 (m n) ω)
    (N : ℝ≥0) (hNm : ∀ n, clock n (m n) ≤ N)
    (Z : Ω → ℝ) (hZm : AEStronglyMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P,
      Tendsto (fun n => Real.exp (-(q * (clock n (K n ω) : ℝ))) *
        W (x + X.X (clock n (K n ω)) ω)) atTop (𝓝 (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω,
        Real.exp (-(q * (clock n (K n ω) : ℝ))) *
          W (x + X.X (clock n (K n ω)) ω) ∂P)
        atTop (𝓝 (∫ ω, Z ω ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (-(q * (clock n (K n ω) : ℝ))) *
      W (x + X.X (clock n (K n ω)) ω)
  have hWmeas : Measurable W :=
    chat03_scale_function_borel_measurable X q W hW
  have hYm : ∀ n, AEStronglyMeasurable (Y n) P := by
    intro n
    obtain ⟨hReserve, hTime⟩ :=
      chat03_grid_stopped_reserve_time_measurable
        X (clock n) (H n) (hH n) lower upper (m n) (K n) (hK n)
    have hDiscount : Measurable (fun ω =>
        Real.exp (-(q * (clock n (K n ω) : ℝ)))) :=
      Real.measurable_exp.comp ((measurable_const.mul hTime).neg)
    have hScale : Measurable (fun ω =>
        W (x + X.X (clock n (K n ω)) ω)) :=
      hWmeas.comp (measurable_const.add hReserve)
    exact (hDiscount.mul hScale).aestronglyMeasurable
  have hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω := by
    intro n
    apply Filter.Eventually.of_forall
    intro ω
    dsimp [Y]
    apply mul_nonneg (Real.exp_nonneg _)
    by_cases hy : 0 ≤ x + X.X (clock n (K n ω)) ω
    · exact hW.2.1 _ hy
    · simp [hW.1 _ (lt_of_not_ge hy)]
  let C : ℝ := ((X.ψ θ - q)⁻¹)^2 *
    Real.exp (2 * θ * (x + 1) + (N : ℝ) * max (X.ψ (2 * θ)) 0)
  have hC : 0 ≤ C :=
    mul_nonneg (sq_nonneg _) (le_of_lt (Real.exp_pos _))
  have hY2 : ∀ n, Integrable (fun ω => (Y n ω)^2) P ∧
      ∫ ω, (Y n ω)^2 ∂P ≤ C := by
    intro n
    simpa [Y, C] using
      (chat03_bounded_grid_l2_unconditional X q hq W hW θ x hθ hψ
        (clock n) (hc n) (hc0 n) (H n) (hH n)
        lower upper (m n) (K n) (hK n) N (hNm n))
  exact nonnegative_integral_tendsto_of_uniform_second_moment
    Y Z hYm hY0 hZm hconv C hC hY2
