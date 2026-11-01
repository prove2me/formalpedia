-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_largejump_weighted_section_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T10:04:43.489303+00:00
-- url     : https://prove2.me/submissions/476735e9-ba2b-4ae7-b552-7ea20e3da51d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_scale_uncompensated_jump_large_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Large jumps are uncompensated: genuine weighted state-section
    integrability, not only a potentially vacuous Bochner integral inequality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 1 ≤ r) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
      (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) ≤
        (X.ψ θ - q)⁻¹ := by
  have hy : -r ≤ (-1 : ℝ) := by linarith
  have hshift := scaleFunction_shiftedLaplace_integrable
    X q W hW θ (-r) hθ hqθ (by linarith)
  have hbase := scaleFunction_shiftedLaplace_integrable
    X q W hW θ 0 hθ hqθ (by norm_num)
  have hdiff : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * (W (x-r) - W x))
      (Ioi (0 : ℝ)) volume := by
    convert hshift.sub hbase using 1
    funext x
    simp only [Pi.sub_apply, add_zero]
    rw [show x + -r = x - r by ring]
    ring
  have habs : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * |W (x-r) - W x|)
      (Ioi (0 : ℝ)) volume := by
    change Integrable (fun x : ℝ => Real.exp (-(θ * x)) *
      |W (x-r) - W x|) (volume.restrict (Ioi (0 : ℝ)))
    convert hdiff.abs using 1
    funext x
    simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
  have heq (x : ℝ) :
      SpectrallyNegativeLevy.generatorIntegrand W x (-r) =
        W (x-r) - W x := by
    convert generatorIntegrand_large_negative W x (-r) hy using 1
    ring
  have hint : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|)
      (Ioi (0 : ℝ)) volume := by
    convert habs using 1
    funext x
    rw [heq]
  refine ⟨hint, ?_⟩
  calc
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
      |SpectrallyNegativeLevy.generatorIntegrand W x (-r)|) =
      ∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        |W x - W (x-r)| := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [heq]
      rw [abs_sub_comm]
    _ ≤ (X.ψ θ - q)⁻¹ :=
      chat07_scale_uncompensated_jump_large_uniform_bound
        X q W hW θ hθ hqθ r hr
