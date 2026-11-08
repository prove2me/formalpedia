-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_affine_singular_large_reserve_generator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:41:44.793445+00:00
-- url     : https://prove2.me/submissions/b3f659d0-c218-422c-be70-22f0869d3193

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_large_reserve_integrand_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The compensated jump term is integrable at every reserve at least one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (x : ℝ) (hx : 1 ≤ x) :
    X.GeneratorIntegrable
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x := by
  let ν : Measure ℝ := volume.withDensity (fun z : ℝ =>
    if z ∈ Ioo (-1 : ℝ) 0
    then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)
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
  have hmeas : Measurable (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0) :=
    Measurable.ite isOpen_Ioo.measurableSet
      (ENNReal.measurable_ofReal.comp hpow) measurable_const
  have hsupport : ∀ᵐ z ∂ν, z ∈ Ioo (-1 : ℝ) 0 := by
    apply (ae_withDensity_iff hmeas).2
    apply Filter.Eventually.of_forall
    intro z hne
    by_contra hz
    simp [hz] at hne
  have hzero :
      (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z) =ᵐ[ν]
      (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hsupport] with z hz
    exact avram_a19_affine_singular_large_reserve_integrand_zero x z hx hz
  have hint : Integrable (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z) ν := by
    have hzero_int : Integrable (fun _ : ℝ => (0 : ℝ)) ν := by simp
    exact hzero_int.congr hzero.symm
  change IntegrableOn (SpectrallyNegativeLevy.generatorIntegrand
    (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x) (Iio 0) X.ν
  rw [hν]
  exact hint.integrableOn
