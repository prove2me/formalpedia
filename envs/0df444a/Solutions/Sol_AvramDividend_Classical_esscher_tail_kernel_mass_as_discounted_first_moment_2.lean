-- Prove2me | solution 2 for AvramDividend.Classical.esscher_tail_kernel_mass_as_discounted_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:49:06.163168+00:00
-- url     : https://prove2.me/submissions/c176d10d-203d-4e1e-a45e-aa53c0f22f85

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.FunProp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal


theorem solution
    (μ : Measure ℝ≥0) (φ : ℝ) :
    let μφ : Measure ℝ≥0 :=
      μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))
    let κφ : Measure ℝ :=
      (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ => μφ {z : ℝ≥0 | t < (z : ℝ)})
    κφ Set.univ =
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ := by
  dsimp
  have hf : Measurable (fun z : ℝ≥0 =>
      ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))) := by
    fun_prop
  have hg : Measurable (fun z : ℝ≥0 =>
      ENNReal.ofReal (z : ℝ)) := by
    fun_prop
  have hcast : Measurable (fun z : ℝ≥0 => (z : ℝ)) := by
    fun_prop
  have hnonneg :
      0 ≤ᵐ[μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))]
        (fun z : ℝ≥0 => (z : ℝ)) :=
    Filter.Eventually.of_forall (fun z => z.property)
  have htail :=
    lintegral_eq_lintegral_meas_lt
      (μ.withDensity (fun z : ℝ≥0 =>
        ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
      hnonneg hcast.aemeasurable
  calc
    (volume.restrict (Ioi (0 : ℝ))).withDensity
        (fun t : ℝ =>
          (μ.withDensity (fun z : ℝ≥0 =>
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) Set.univ
        = ∫⁻ t in Ioi (0 : ℝ),
            (μ.withDensity (fun z : ℝ≥0 =>
              ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
              {z : ℝ≥0 | t < (z : ℝ)} := by
              rw [withDensity_apply _ MeasurableSet.univ]
              simp
    _ = ∫⁻ z : ℝ≥0, ENNReal.ofReal (z : ℝ)
        ∂(μ.withDensity (fun z : ℝ≥0 =>
          ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))))) :=
          htail.symm
    _ = ∫⁻ z : ℝ≥0,
        ENNReal.ofReal ((z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ∂μ := by
      rw [lintegral_withDensity_eq_lintegral_mul μ hf hg]
      apply lintegral_congr_ae
      filter_upwards [] with z
      simp only [Pi.mul_apply]
      rw [ENNReal.ofReal_mul' (Real.exp_nonneg _)]
      exact mul_comm _ _
