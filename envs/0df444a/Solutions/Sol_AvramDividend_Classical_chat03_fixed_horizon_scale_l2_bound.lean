-- Prove2me | solution 1 for AvramDividend.Classical.chat03_fixed_horizon_scale_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T17:24:18.116109+00:00
-- url     : https://prove2.me/submissions/5a5969de-74dc-432b-8ad7-93ed11cef3e3

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_finite_horizon_scale_square_compensator_bound
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

/-!
A genuinely mesh-uniform L² estimate under an explicit stopped exponential
moment identity and measurable stopped scale payoff. No killed scale
martingale is assumed. The latter two hypotheses have independent routes
from the published process and the already proved finite-grid lemmas.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (N : ℝ≥0) (T : Ω → ℝ≥0) (Z : Ω → ℝ)
    (hT : ∀ ω, T ω ≤ N)
    (hScaleMeas : AEStronglyMeasurable
      (fun ω => (Real.exp (-(q * (T ω : ℝ))) * W (x + Z ω)) ^ 2) P)
    (hMomentInt : Integrable
      (fun ω => Real.exp (2 * θ * Z ω -
        (T ω : ℝ) * X.ψ (2 * θ))) P)
    (hMomentOne : (∫ ω, Real.exp (2 * θ * Z ω -
      (T ω : ℝ) * X.ψ (2 * θ)) ∂P) = 1) :
    Integrable
      (fun ω => (Real.exp (-(q * (T ω : ℝ))) * W (x + Z ω)) ^ 2) P ∧
    (∫ ω, (Real.exp (-(q * (T ω : ℝ))) * W (x + Z ω)) ^ 2 ∂P) ≤
      ((X.ψ θ - q)⁻¹)^2 *
        Real.exp (2 * θ * (x + 1) +
          (N : ℝ) * max (X.ψ (2 * θ)) 0) := by
  let F : Ω → ℝ := fun ω =>
    (Real.exp (-(q * (T ω : ℝ))) * W (x + Z ω)) ^ 2
  let M : Ω → ℝ := fun ω =>
    Real.exp (2 * θ * Z ω - (T ω : ℝ) * X.ψ (2 * θ))
  let C : ℝ := ((X.ψ θ - q)⁻¹)^2 *
    Real.exp (2 * θ * (x + 1) + (N : ℝ) * max (X.ψ (2 * θ)) 0)
  have hC : 0 ≤ C :=
    mul_nonneg (sq_nonneg _) (Real.exp_nonneg _)
  have hBound : ∀ ω, F ω ≤ C * M ω := by
    intro ω
    exact chat03_finite_horizon_scale_square_compensator_bound
      X q hq W hW θ x (Z ω) hθ hψ N (T ω) (hT ω)
  have hCInt : Integrable (fun ω => C * M ω) P :=
    hMomentInt.const_mul _
  have hFInt : Integrable F P := by
    apply Integrable.mono' hCInt hScaleMeas
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hBound ω
  have hIntLe : (∫ ω, F ω ∂P) ≤ ∫ ω, C * M ω ∂P :=
    integral_mono hFInt hCInt hBound
  rw [integral_const_mul] at hIntLe
  change (∫ ω, M ω ∂P) = 1 at hMomentOne
  rw [hMomentOne, mul_one] at hIntLe
  exact ⟨hFInt, hIntLe⟩