-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_volterra_residual_continuous_on_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T18:59:59.130826+00:00
-- url     : https://prove2.me/submissions/561cbc0c-6946-4757-bff0-801be4607927

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_positive_indicator_continuous
import Theorems.Thm_AvramDividend_Classical_gaussian_native_levy_esscher_double_tail_integrable
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_continuousOn_locally_integrable_left
import Theorems.Thm_AvramDividend_Classical_positive_causal_integral_eq_posConvolution
import Mathlib.Analysis.Convolution

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- The Gaussian Esscher Volterra residual is continuous on positive times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x)
    (a β : ℝ) (K : ℝ → ℝ)
    (ha : a = X.σ ^ 2 / 2)
    (hβ : β =
      X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
        X.σ ^ 2 * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
          ∂(X.ν.map (fun y : ℝ => -y))))
    (hK : K = fun t : ℝ =>
      (∫⁻ z : ℝ,
        if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
        else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal) :
    ContinuousOn (fun x : ℝ =>
      a * V x +
        (∫ s in Ioc (0 : ℝ) x,
          (β + K (x - s)) * V s ∂volume)) (Ioi (0 : ℝ)) := by
  have hKi : IntegrableOn K (Ioi (0 : ℝ)) volume := by
    rw [hK]
    exact gaussian_native_levy_esscher_double_tail_integrable X φ hφ
  have hVc : Continuous ((Ioi (0 : ℝ)).indicator V) :=
    gaussian_esscher_positive_indicator_continuous
      X q hq W hW hσ φ V hV
  have hloc (R : ℝ) (_hR : 0 < R) :
      IntegrableOn (fun t : ℝ => β + K t) (Ioc (0 : ℝ) R) volume := by
    have hc : IntegrableOn (fun _ : ℝ => β) (Ioc (0 : ℝ) R) volume := by
      exact integrableOn_const
        (hs := (measure_Ioc_lt_top : volume (Ioc (0 : ℝ) R) < ⊤).ne)
    have hKl : IntegrableOn K (Ioc (0 : ℝ) R) volume :=
      hKi.mono_set (by intro t ht; exact ht.1)
    exact hc.add hKl
  have hconv : ContinuousOn
      (MeasureTheory.posConvolution (fun t : ℝ => β + K t) V
        (ContinuousLinearMap.mul ℝ ℝ) volume) (Ioi (0 : ℝ)) :=
    positive_causal_convolution_continuousOn_locally_integrable_left
      (fun t : ℝ => β + K t) V hloc hVc
  have hVpos : ContinuousOn V (Ioi (0 : ℝ)) := by
    intro x hx
    have hev : V =ᶠ[nhdsWithin x (Ioi (0 : ℝ))]
        ((Ioi (0 : ℝ)).indicator V) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (Set.indicator_of_mem hy V).symm
    exact hVc.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem hev hx
  have hsum : ContinuousOn (fun x : ℝ => a * V x +
      MeasureTheory.posConvolution (fun t : ℝ => β + K t) V
        (ContinuousLinearMap.mul ℝ ℝ) volume x) (Ioi (0 : ℝ)) :=
    (continuousOn_const.mul hVpos).add hconv
  intro x hx
  have hev : (fun y : ℝ => a * V y +
      ∫ s in Ioc (0 : ℝ) y, (β + K (y - s)) * V s ∂volume) =ᶠ[
        nhdsWithin x (Ioi (0 : ℝ))]
      (fun y : ℝ => a * V y +
        MeasureTheory.posConvolution (fun t : ℝ => β + K t) V
          (ContinuousLinearMap.mul ℝ ℝ) volume y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact congrArg (fun z : ℝ => a * V y + z)
      (positive_causal_integral_eq_posConvolution
        (fun t : ℝ => β + K t) V y hy)
  exact (hsum x hx).congr_of_eventuallyEq_of_mem hev hx
