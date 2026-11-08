-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_singular_subunit_original_generator_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:20:12.081856+00:00
-- url     : https://prove2.me/submissions/7302f19c-ba0e-4e76-9f7c-e0720dbddd05

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_deriv_one
import Theorems.Thm_AvramDividend_Classical_avram_gen14_affine_singular_density_generator_integral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact compensated generator of the zero-extended affine candidate below one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 0 < x) (hx1 : x < 1) :
    X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x =
      X.c + (2 * (1 - x ^ (1 / 2 : ℝ)) -
        (1 + x) * (2 * (x ^ (-(1 / 2 : ℝ)) - 1))) := by
  have hneg : ∀ᵐ z ∂X.ν, z ∈ Iio (0 : ℝ) := by
    apply (ae_iff).2
    simpa [Iio, Ici, not_lt] using X.ν_Ici
  have hrestrict : X.ν.restrict (Iio (0 : ℝ)) = X.ν :=
    Measure.restrict_eq_self_of_ae_mem hneg
  have hjump : (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z ∂X.ν) =
      2 * (1 - x ^ (1 / 2 : ℝ)) -
        (1 + x) * (2 * (x ^ (-(1 / 2 : ℝ)) - 1)) := by
    change (∫ z, SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z
        ∂(X.ν.restrict (Iio (0 : ℝ)))) = _
    rw [hrestrict, hν]
    exact avram_gen14_affine_singular_density_generator_integral x hx hx1
  have hd : deriv (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x = 1 :=
    avram_a19_affine_zero_extension_deriv_one x hx
  have hσ : X.σ = 0 := hBV.1
  simp [SpectrallyNegativeLevy.generator, hσ, hd, hjump]
