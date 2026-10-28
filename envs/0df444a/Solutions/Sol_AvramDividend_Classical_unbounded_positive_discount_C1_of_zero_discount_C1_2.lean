-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_positive_discount_C1_of_zero_discount_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:48:35.667982+00:00
-- url     : https://prove2.me/submissions/04eb7f88-7c8b-4804-8ad9-ca103d0c46c5

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_scale_weighted_derivative_correction_integrable
import Theorems.Thm_AvramDividend_Classical_exp_weighted_scale_hasDerivAt
import Theorems.Thm_AvramDividend_Classical_integrable_derivative_primitive_at_zero
import Theorems.Thm_AvramDividend_Classical_causal_resolvent_C1_of_exponential_weighting
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Propagate C1 regularity from the zero-discount scale to every positive-discount scale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (hW₀C1 : ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)))
    (q : ℝ) (hq : 0 < q)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)) := by
  have hθ0 : 0 < X.ψ θ := lt_trans hq hqθ
  have hWqL1 : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * Wq x)
      (Ioi (0 : ℝ)) volume :=
    (hWq.2.2.2.2 θ hθ hqθ).1
  have hkL1 : IntegrableOn
      (fun x : ℝ =>
        Real.exp (-(θ * x)) * (deriv W₀ x - θ * W₀ x))
      (Ioi (0 : ℝ)) volume :=
    scale_weighted_derivative_correction_integrable
      X 0 W₀ hW₀ θ hθ hθ0
  have hW₀zero : W₀ 0 = 0 :=
    unbounded_scale_zero_origin_nonnegative_discount
      X hnbv 0 (le_refl 0) W₀ hW₀
  have hgcont : ContinuousOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W₀ x) (Ici 0) := by
    have he : Continuous (fun x : ℝ => Real.exp (-(θ * x))) := by
      fun_prop
    exact he.continuousOn.mul hW₀.2.2.1
  have hg0 : Real.exp (-(θ * (0 : ℝ))) * W₀ 0 = 0 := by
    simp [hW₀zero]
  have hGprim : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x,
        Real.exp (-(θ * t)) * (deriv W₀ t - θ * W₀ t) ∂volume) =
          Real.exp (-(θ * x)) * W₀ x := by
    apply integrable_derivative_primitive_at_zero
      (fun x : ℝ => Real.exp (-(θ * x)) * W₀ x)
      (fun x : ℝ => Real.exp (-(θ * x)) * (deriv W₀ x - θ * W₀ x))
      hg0 hgcont hkL1
    intro x hx
    have hc : ContDiffAt ℝ 1 W₀ x :=
      hW₀C1.contDiffAt (isOpen_Ioi.mem_nhds hx)
    exact exp_weighted_scale_hasDerivAt W₀ θ x
      (hc.differentiableAt (by norm_num))
  have hres : ∀ x : ℝ, 0 < x →
      Wq x = W₀ x -
        (-q) * (∫ s in Ioc (0 : ℝ) x,
          Wq (x - s) * W₀ s ∂volume) := by
    intro x hx
    have hr := unbounded_scale_resolvent_convolution
      X hnbv 0 q (le_refl (0 : ℝ)) hq.le W₀ Wq hW₀ hWq x hx
    have hI : (∫ s in Ioc (0 : ℝ) x, W₀ s * Wq (x - s) ∂volume) =
        ∫ s in Ioc (0 : ℝ) x, Wq (x - s) * W₀ s ∂volume := by
      congr 1
      funext s
      ring
    rw [sub_zero, hI] at hr
    linarith
  exact causal_resolvent_C1_of_exponential_weighting
    Wq W₀
    (fun x : ℝ => Real.exp (-(θ * x)) * (deriv W₀ x - θ * W₀ x))
    (-q) θ hWq.2.2.1 hWqL1 hkL1 hGprim hW₀C1 hres
