-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_scale_real_volterra_laplace_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:24:26.267623+00:00
-- url     : https://prove2.me/submissions/ed10eefd-3540-4c62-aca3-40000f9cdc65

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_strictly_above_root
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_gaussian_native_esscher_real_kernel_denominator
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_scale_laplace_of_positive_agreement

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
    (θ * (X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
      X.σ ^ 2 * φ +
      (∫ z in Ioi (0 : ℝ),
        (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
        ∂(X.ν.map (fun y : ℝ => -y)))) +
      (X.σ ^ 2 / 2) * θ ^ 2 +
      θ ^ 2 * (∫ t : ℝ, Real.exp (-θ * t) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂(X.ν.map (fun y : ℝ => -y))).toReal ∂volume)) *
      (∫ s in Ioi (0 : ℝ), Real.exp (-(θ * s)) * V s ∂volume) = 1 := by
  have hν : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono_set (Set.subset_univ _))
      (by simpa only [Measure.restrict_univ] using X.ν_integrable)
  have hpush :=
    gaussian_levy_square_integrable_neg_pushforward X.ν hν
  have hψ : q < X.ψ (φ + θ) :=
    gaussian_esscher_psi_strictly_above_root
      X q φ θ hq hφ hθ hσ hroot hpush
  have hLap :
      (∫ s in Ioi (0 : ℝ), Real.exp (-(θ * s)) * V s ∂volume) =
      (X.ψ (φ + θ) - q)⁻¹ := by
    have hψ' : q < X.ψ (θ + φ) := by
      simpa only [add_comm θ φ] using hψ
    have h := (esscher_tilted_scale_laplace_of_positive_agreement
      X q W hW φ θ (add_nonneg hθ.le hφ.le) hψ' V hV).2
    simpa only [add_comm θ φ] using h
  have hdenom := gaussian_native_esscher_real_kernel_denominator
    X q φ θ hφ hθ hroot
  rw [hLap, ← hdenom]
  exact mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hψ))
