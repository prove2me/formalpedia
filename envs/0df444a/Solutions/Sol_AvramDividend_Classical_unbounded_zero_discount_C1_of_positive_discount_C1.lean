-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_zero_discount_C1_of_positive_discount_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T21:18:24.58791+00:00
-- url     : https://prove2.me/submissions/fd0fdbfc-2eae-4edd-a922-002f8d4e320b

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_resolvent_convolution
import Theorems.Thm_AvramDividend_Classical_unbounded_scale_zero_origin_nonnegative_discount
import Theorems.Thm_AvramDividend_Classical_causal_convolution_time_reversal
import Theorems.Thm_AvramDividend_Classical_scale_weighted_derivative_correction_integrable
import Theorems.Thm_AvramDividend_Classical_exp_weighted_scale_hasDerivAt
import Theorems.Thm_AvramDividend_Classical_integrable_derivative_primitive_at_zero
import Theorems.Thm_AvramDividend_Classical_causal_resolvent_C1_of_exponential_weighting
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Transfer positive-discount scale C1 regularity down to zero discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (W₀ : ℝ → ℝ) (hW₀ : IsScaleFunction X 0 W₀)
    (q : ℝ) (hq : 0 < q)
    (Wq : ℝ → ℝ) (hWq : IsScaleFunction X q Wq)
    (hWqC1 : ContDiffOn ℝ 1 Wq (Ioi (0 : ℝ)))
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    ContDiffOn ℝ 1 W₀ (Ioi (0 : ℝ)) := by
  have hθ0 : 0 < X.ψ θ := lt_trans hq hqθ
  have hW₀L1 : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W₀ x)
      (Ioi (0 : ℝ)) volume :=
    (hW₀.2.2.2.2 θ hθ hθ0).1
  have hkL1 : IntegrableOn
      (fun x : ℝ =>
        Real.exp (-(θ * x)) * (deriv Wq x - θ * Wq x))
      (Ioi (0 : ℝ)) volume :=
    scale_weighted_derivative_correction_integrable X q Wq hWq θ hθ hqθ
  have hq0 : Wq 0 = 0 :=
    unbounded_scale_zero_origin_nonnegative_discount X hnbv q hq.le Wq hWq
  have hgcont : ContinuousOn
      (fun x : ℝ => Real.exp (-(θ * x)) * Wq x) (Ici (0 : ℝ)) := by
    have he : Continuous (fun x : ℝ => Real.exp (-(θ * x))) := by
      fun_prop
    exact he.continuousOn.mul hWq.2.2.1
  have hg0 : Real.exp (-(θ * (0 : ℝ))) * Wq 0 = 0 := by
    simp [hq0]
  have hGprim : ∀ x : ℝ, 0 < x →
      (∫ t in Ioc (0 : ℝ) x,
        Real.exp (-(θ * t)) * (deriv Wq t - θ * Wq t) ∂volume) =
          Real.exp (-(θ * x)) * Wq x := by
    apply integrable_derivative_primitive_at_zero
      (fun x : ℝ => Real.exp (-(θ * x)) * Wq x)
      (fun x : ℝ => Real.exp (-(θ * x)) * (deriv Wq x - θ * Wq x))
      hg0 hgcont hkL1
    intro x hx
    have hc : ContDiffAt ℝ 1 Wq x :=
      hWqC1.contDiffAt (isOpen_Ioi.mem_nhds hx)
    exact exp_weighted_scale_hasDerivAt Wq θ x
      (hc.differentiableAt (by norm_num))
  have hres : ∀ x : ℝ, 0 < x →
      W₀ x = Wq x -
        q * (∫ s in Ioc (0 : ℝ) x,
          W₀ (x - s) * Wq s ∂volume) := by
    intro x hx
    have hr := unbounded_scale_resolvent_convolution
      X hnbv 0 q (le_refl (0 : ℝ)) hq.le W₀ Wq hW₀ hWq x hx
    have hflip := causal_convolution_time_reversal W₀ Wq x hx.le
    rw [sub_zero] at hr
    rw [hflip]
    linarith
  exact causal_resolvent_C1_of_exponential_weighting
    W₀ Wq
    (fun x : ℝ => Real.exp (-(θ * x)) * (deriv Wq x - θ * Wq x))
    q θ hW₀.2.2.1 hW₀L1 hkL1 hGprim hWqC1 hres
