-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_integrator_new_genuine_perpetual_cdf_scale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:05:49.438752+00:00
-- url     : https://prove2.me/submissions/e9991924-5f67-45ab-8361-6fbb01c0151a

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_probability_support_laplace
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_perpetual_infimum_wiener_hopf_scalar
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_integrator_new_supported_infimum_laplace_identifies_scale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ (ν : Measure ℝ) (m : ℝ),
      IsProbabilityMeasure ν ∧ 0 < m ∧
      (∀ x : ℝ, ν (Iic x) =
        (⨅ t : ℝ≥0, ENNReal.ofReal
          (∫ ω, ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
            (fun ω => Real.exp (φ * X.X t ω -
              (t : ℝ) * laplaceExponent X.c X.σ X.ν φ)) ω ∂P))) ∧
      (∀ x : ℝ, 0 < x → ν (Iic x) =
        ENNReal.ofReal (m * Real.exp (-(φ * x)) * W x)) := by
  classical
  obtain ⟨ν₀, hν₀P, hν₀Supp, hν₀CDF, _, _⟩ :=
    esscher_positive_root_perpetual_probability_support_laplace
      X q φ hq hφ hroot
  obtain ⟨ν, m, hνP, hm, hνCDF, hνLap⟩ :=
    esscher_positive_root_perpetual_infimum_wiener_hopf_scalar
      X q φ hq hφ hroot
  letI : IsProbabilityMeasure ν := hνP
  letI : IsProbabilityMeasure ν₀ := hν₀P
  have hνEq : ν = ν₀ := by
    apply Measure.ext_of_Iic ν ν₀
    intro x
    exact (hνCDF x).trans (hν₀CDF x).symm
  have hνSupp : ν (Iio 0) = 0 := by
    rw [hνEq]
    exact hν₀Supp
  have hscale :=
    avram_ws01e_integrator_new_supported_infimum_laplace_identifies_scale
      X q φ hq hφ hroot ν hνSupp m hm hνLap W hW
  exact ⟨ν, m, hνP, hm, hνCDF, hscale⟩
