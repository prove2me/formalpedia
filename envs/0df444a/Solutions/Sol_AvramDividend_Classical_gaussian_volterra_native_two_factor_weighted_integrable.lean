-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_volterra_native_two_factor_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T17:14:47.541986+00:00
-- url     : https://prove2.me/submissions/6d3dfc8f-982f-4453-a662-f463bc084c96

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_strictly_above_root
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_of_positive_agreement
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_weighted_integrable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x → V x = Real.exp (-(φ * x)) * W x)
    (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun s : ℝ => Real.exp (-(θ * s)) * V s)
      (Ioi (0 : ℝ)) volume ∧
    IntegrableOn (fun t : ℝ => Real.exp (-(θ * t)) *
      (∫⁻ z : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z)))
         else 0) ∂(X.ν.map (fun y : ℝ => -y))).toReal)
      (Ioi (0 : ℝ)) volume := by
  have hneg : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono_set (Set.subset_univ _))
      (by simpa only [Measure.restrict_univ] using X.ν_integrable)
  have hpush := gaussian_levy_square_integrable_neg_pushforward X.ν hneg
  have hψ : q < X.ψ (φ + θ) :=
    gaussian_esscher_psi_strictly_above_root
      X q φ θ hq hφ hθ hσ hroot hpush
  have hψ' : q < X.ψ (θ + φ) := by
    simpa only [add_comm θ φ] using hψ
  have hVint : IntegrableOn
      (fun s : ℝ => Real.exp (-(θ * s)) * V s)
      (Ioi (0 : ℝ)) volume :=
    (esscher_tilted_scale_laplace_of_positive_agreement
      X q W hW φ θ (add_nonneg hθ.le hφ.le) hψ' V hV).1
  let μ : Measure ℝ := X.ν.map (fun y : ℝ => -y)
  letI : SigmaFinite μ :=
    gaussian_negative_jump_pushforward_sigmaFinite X.ν X.ν_Ici hneg
  have hKint := gaussian_double_tail_real_kernel_weighted_integrable
    μ φ θ hφ hθ.le hpush
  exact ⟨hVint, hKint⟩
