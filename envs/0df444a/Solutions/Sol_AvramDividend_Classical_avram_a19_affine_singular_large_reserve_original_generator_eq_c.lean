-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_singular_large_reserve_original_generator_eq_c
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:17:14.783732+00:00
-- url     : https://prove2.me/submissions/655fa1f8-081b-423c-aa08-d97b9523ba89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_deriv_one
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_integrand_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original generator's compensated jump integral vanishes above reserve one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 1 ≤ x) :
    X.generator (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x = X.c := by
  let density : ℝ → ℝ≥0∞ := fun z =>
    if z ∈ Ioo (-1 : ℝ) 0
    then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0
  have hpow : Measurable (fun z : ℝ => |z| ^ (-(3 / 2 : ℝ))) := by
    have hlog : Measurable (fun z : ℝ => Real.log |z|) :=
      Real.measurable_log.comp (measurable_id.abs)
    have hexp : Measurable
        (fun z : ℝ => Real.exp (Real.log |z| * (-(3 / 2 : ℝ)))) :=
      Real.measurable_exp.comp (hlog.mul measurable_const)
    have hset : MeasurableSet {z : ℝ | |z| = 0} :=
      (measurable_id.abs) (measurableSet_singleton (0 : ℝ))
    have heq : (fun z : ℝ => |z| ^ (-(3 / 2 : ℝ))) =
        (fun z : ℝ => if |z| = 0 then 0
          else Real.exp (Real.log |z| * (-(3 / 2 : ℝ)))) := by
      funext z
      rw [Real.rpow_def_of_nonneg (abs_nonneg z)]
      norm_num
    rw [heq]
    exact Measurable.ite hset measurable_const hexp
  have hmeas : Measurable density :=
    Measurable.ite isOpen_Ioo.measurableSet
      (ENNReal.measurable_ofReal.comp hpow) measurable_const
  have hsupport : ∀ᵐ z ∂X.ν, z ∈ Ioo (-1 : ℝ) 0 := by
    rw [hν]
    apply (ae_withDensity_iff hmeas).2
    apply Filter.Eventually.of_forall
    intro z hne
    by_contra hz
    simp [density, hz] at hne
    exact hz ⟨hne.1, hne.2.1⟩
  have hzero : ∀ᵐ z ∂X.ν,
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z = 0 := by
    filter_upwards [hsupport] with z hz
    exact avram_a19_affine_singular_large_reserve_integrand_zero x z hx hz
  have hint : (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z ∂X.ν) = 0 := by
    calc
      _ = ∫ _z in Iio (0 : ℝ), (0 : ℝ) ∂X.ν := by
        apply integral_congr_ae
        exact ae_restrict_of_ae hzero
      _ = 0 := by simp
  have hd : deriv (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x = 1 :=
    avram_a19_affine_zero_extension_deriv_one x (lt_of_lt_of_le zero_lt_one hx)
  have hσ : X.σ = 0 := hBV.1
  simp [SpectrallyNegativeLevy.generator, hσ, hd, hint]
