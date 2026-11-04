-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:17:54.828842+00:00
-- url     : https://prove2.me/submissions/45b8f58b-7978-4cb9-b8f5-60d83b60ea80

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact discounted original stopped Lévy exponential is genuinely integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (q : ℝ) (hq : X.ψ θ ≤ q)
    (τ : Ω → ℝ≥0)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω => Real.exp
      (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P := by
  have hmean :=
    avram_p4_f_assembly_original_rightCont_bounded_stop_esscher_likelihood_mean_one
      X θ hθ τ hstop H hbound
  have hgi : Integrable
      (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ)) P :=
    integrable_of_integral_eq_one hmean
  have hfactor : Measurable
      (fun ω => Real.exp ((X.ψ θ - q) * (τ ω : ℝ))) :=
    Real.measurable_exp.comp (measurable_const.mul hτmeas)
  have hfun : (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) =
      (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) *
        Real.exp ((X.ψ θ - q) * (τ ω : ℝ))) := by
    funext ω
    rw [← Real.exp_add]
    congr 1
    ring
  have hfmeas : AEStronglyMeasurable
      (fun ω => Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)) P := by
    rw [hfun]
    exact hgi.aestronglyMeasurable.fun_mul hfactor.aestronglyMeasurable
  have hdom : ∀ᵐ ω ∂P,
      ‖Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * q)‖ ≤
        Real.exp (θ * X.X (τ ω) ω - (τ ω : ℝ) * X.ψ θ) := by
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have ht : (0 : ℝ) ≤ (τ ω : ℝ) := NNReal.coe_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hq ht
    linarith
  exact hgi.mono' hfmeas hdom
