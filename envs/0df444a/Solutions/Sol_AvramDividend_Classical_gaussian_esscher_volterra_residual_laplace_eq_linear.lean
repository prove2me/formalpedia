-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_volterra_residual_laplace_eq_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T18:01:45.949344+00:00
-- url     : https://prove2.me/submissions/ec66bff2-dfac-48cf-ad40-219d8321b95d

import Theorems.Thm_AvramDividend_Classical_gaussian_volterra_native_two_factor_weighted_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_scale_real_volterra_laplace_product
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_integrable
import Theorems.Thm_AvramDividend_Classical_positive_causal_convolution_laplace_product
import Theorems.Thm_AvramDividend_Classical_positive_laplace_constant_reference

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The Gaussian Esscher Volterra residual has the Laplace transform of x. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ) (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (a β : ℝ) (K : ℝ → ℝ) (ha : a = X.σ ^ 2 / 2)
    (hβ : β = X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ + (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
        ∂(X.ν.map (fun y : ℝ => -y))))
    (hK : K = fun t : ℝ => (∫⁻ z : ℝ,
      if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
      else 0 ∂(X.ν.map (fun y : ℝ => -y))).toReal)
    (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) *
      (a * V x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * V s ∂volume))) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      (a * V x + (∫ s in Ioc (0 : ℝ) x,
        (β + K (x - s)) * V s ∂volume)) ∂volume) = (1 / θ) ^ 2 := by
  have hTwo := gaussian_volterra_native_two_factor_weighted_integrable
    X q hq W hW hσ φ hφ hroot V hV θ hθ
  have hVW := hTwo.1
  have hKW : IntegrableOn (fun t : ℝ => Real.exp (-(θ*t)) * K t)
      (Ioi (0:ℝ)) volume := by simpa only [hK] using hTwo.2
  have hEW : IntegrableOn (fun t : ℝ => Real.exp (-(θ*t)))
      (Ioi (0:ℝ)) volume := (positive_laplace_constant_reference θ hθ).1
  have hβW : IntegrableOn (fun t : ℝ => Real.exp (-(θ*t)) * β)
      (Ioi (0:ℝ)) volume := by
    change Integrable (fun t : ℝ => Real.exp (-(θ*t))*β) (volume.restrict (Ioi (0:ℝ)))
    simpa only [mul_comm β] using hEW.const_mul β
  have hGW : IntegrableOn (fun t : ℝ => Real.exp (-(θ*t)) * (β+K t))
      (Ioi (0:ℝ)) volume := by
    have heq : (fun t : ℝ => Real.exp (-(θ*t))*(β+K t)) =
        (fun t : ℝ => Real.exp (-(θ*t))*β) + (fun t : ℝ => Real.exp (-(θ*t))*K t) := by
      funext t; dsimp; ring
    rw [heq]
    exact hβW.add hKW
  have hSwap : ∀ x : ℝ, (∫ s in Ioc (0:ℝ) x,
      V s * (β+K (x-s)) ∂volume) =
      (∫ s in Ioc (0:ℝ) x, (β+K (x-s))*V s ∂volume) := by
    intro x; congr 1; funext s; ring
  have hCI : IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) *
      (∫ s in Ioc (0:ℝ) x, (β+K (x-s))*V s ∂volume))
      (Ioi (0:ℝ)) volume := by
    convert positive_causal_convolution_laplace_integrable V (fun t => β+K t) θ hVW hGW using 1
    ext x; exact congrArg (Real.exp (-(θ*x)) * ·) (hSwap x).symm
  have hAV : IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) * (a*V x))
      (Ioi (0:ℝ)) volume := by
    change Integrable (fun x : ℝ => Real.exp (-(θ*x))*(a*V x)) (volume.restrict (Ioi (0:ℝ)))
    have heq : (fun x : ℝ => Real.exp (-(θ*x))*(a*V x)) = (fun x : ℝ => a*(Real.exp (-(θ*x))*V x)) := by
      funext x; ring
    rw [heq]
    exact hVW.const_mul a
  let LV : ℝ := ∫ x in Ioi (0:ℝ), Real.exp (-(θ*x))*V x ∂volume
  let LK : ℝ := ∫ t : ℝ, Real.exp (-θ*t)*K t ∂volume
  have hKLap : (∫ t in Ioi (0:ℝ), Real.exp (-(θ*t))*K t ∂volume) = LK := by
    unfold LK
    simp only [neg_mul]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have ht0 : t ≤ 0 := le_of_not_gt (by simpa only [mem_Ioi] using ht)
    have hK0 : K t = 0 := by
      simpa only [hK] using (gaussian_double_tail_real_kernel_zero_nonpositive
        (X.ν.map (fun y : ℝ => -y)) φ t ht0)
    rw [hK0, mul_zero]
  have hConstLap : (∫ t in Ioi (0:ℝ),
      Real.exp (-(θ*t))*β ∂volume) = β/θ := by
    calc
      _ = β * (∫ t in Ioi (0:ℝ), Real.exp (-(θ*t)) ∂volume) := by
        rw [← integral_const_mul]
        congr 1
        funext t; ring
      _ = β/θ := by rw [(positive_laplace_constant_reference θ hθ).2]; ring
  have hGLap : (∫ t in Ioi (0:ℝ),
      Real.exp (-(θ*t))*(β+K t) ∂volume) = β/θ+LK := by
    calc
      _ = ∫ t in Ioi (0:ℝ), (Real.exp (-(θ*t))*β +
          Real.exp (-(θ*t))*K t) ∂volume := by congr 1; funext t; ring
      _ = (∫ t in Ioi (0:ℝ), Real.exp (-(θ*t))*β ∂volume) +
          (∫ t in Ioi (0:ℝ), Real.exp (-(θ*t))*K t ∂volume) :=
            integral_add hβW hKW
      _ = β/θ+LK := by rw [hConstLap, hKLap]
  have hConvLap : (∫ x in Ioi (0:ℝ), Real.exp (-(θ*x)) *
      (∫ s in Ioc (0:ℝ) x, (β+K (x-s))*V s ∂volume) ∂volume) =
      LV * (β/θ+LK) := by
    calc
      _ = ∫ x in Ioi (0:ℝ), Real.exp (-(θ*x)) *
          (∫ s in Ioc (0:ℝ) x, V s*(β+K (x-s)) ∂volume) ∂volume := by
            congr 1; funext x; rw [hSwap x]
      _ = LV * (∫ t in Ioi (0:ℝ),
          Real.exp (-(θ*t))*(β+K t) ∂volume) :=
            positive_causal_convolution_laplace_product
              V (fun t => β+K t) θ hVW hGW
      _ = LV*(β/θ+LK) := by rw [hGLap]
  have hALap : (∫ x in Ioi (0:ℝ),
      Real.exp (-(θ*x))*(a*V x) ∂volume) = a*LV := by
    dsimp [LV]
    calc
      _ = ∫ x in Ioi (0:ℝ), a*(Real.exp (-(θ*x))*V x) ∂volume := by
        congr 1; funext x; ring
      _ = a * (∫ x in Ioi (0:ℝ),
          Real.exp (-(θ*x))*V x ∂volume) := integral_const_mul a _
  have hP : (θ*β+a*θ^2+θ^2*LK)*LV = 1 := by
    convert (gaussian_esscher_scale_real_volterra_laplace_product
      X q hq W hW hσ φ hφ hroot V hV θ hθ) using 1
      <;> simp only [LV, LK, ha, hβ, hK, neg_mul]
      <;> ring
  refine ⟨?_, ?_⟩
  · have heq : (fun x : ℝ => Real.exp (-(θ*x)) * (a*V x +
          (∫ s in Ioc (0:ℝ) x, (β+K (x-s))*V s ∂volume))) =
          (fun x : ℝ => Real.exp (-(θ*x))*(a*V x)) +
          (fun x : ℝ => Real.exp (-(θ*x))*(∫ s in Ioc (0:ℝ) x,
            (β+K (x-s))*V s ∂volume)) := by
        funext x; dsimp; ring
    rw [heq]
    exact hAV.add hCI
  · calc
      _ = ∫ x in Ioi (0:ℝ),
          (Real.exp (-(θ*x))*(a*V x) +
            Real.exp (-(θ*x))*(∫ s in Ioc (0:ℝ) x,
              (β+K (x-s))*V s ∂volume)) ∂volume := by
            congr 1; funext x; ring
      _ = (∫ x in Ioi (0:ℝ), Real.exp (-(θ*x))*(a*V x) ∂volume) +
          (∫ x in Ioi (0:ℝ), Real.exp (-(θ*x))*
            (∫ s in Ioc (0:ℝ) x,
              (β+K (x-s))*V s ∂volume) ∂volume) := integral_add hAV hCI
      _ = a*LV + LV*(β/θ+LK) := by rw [hALap, hConvLap]
      _ = ((θ*β+a*θ^2+θ^2*LK)*LV)/θ^2 := by field_simp; ring
      _ = (1/θ)^2 := by rw [hP]; ring
