-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a49_positive_exponential_tail_chernoff_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:21:10.956709+00:00
-- url     : https://prove2.me/submissions/70e45da8-c587-4402-8b1a-07a79e47df72

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a48_positive_exponential_tail_chernoff_majorant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Positive exponential source excursions have a tunable integrated Chernoff bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Ω → ℝ) (hZ : Measurable Z)
    (θ r δ : ℝ) (hr : 0 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal
      (if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) ∂P) ≤
      ENNReal.ofReal (Real.exp (-r * δ)) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ + r) * Z ω)) ∂P) := by
  have hf : Measurable (fun ω : Ω =>
      ENNReal.ofReal (Real.exp ((θ + r) * Z ω))) := by
    fun_prop
  have hPoint (ω : Ω) :
      ENNReal.ofReal
        (if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) ≤
      ENNReal.ofReal (Real.exp (-r * δ)) *
        ENNReal.ofReal (Real.exp ((θ + r) * Z ω)) := by
    calc
      ENNReal.ofReal
        (if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) ≤
          ENNReal.ofReal
            (Real.exp (-r * δ) * Real.exp ((θ + r) * Z ω)) :=
        ENNReal.ofReal_le_ofReal
          (avram_ga_a48_positive_exponential_tail_chernoff_majorant
            (Z ω) θ r δ hr)
      _ = ENNReal.ofReal (Real.exp (-r * δ)) *
            ENNReal.ofReal (Real.exp ((θ + r) * Z ω)) :=
        ENNReal.ofReal_mul (Real.exp_pos _).le
  calc
    (∫⁻ ω, ENNReal.ofReal
      (if δ ≤ Z ω then Real.exp (θ * Z ω) else 0) ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-r * δ)) *
        ENNReal.ofReal (Real.exp ((θ + r) * Z ω)) ∂P) :=
      lintegral_mono hPoint
    _ = ENNReal.ofReal (Real.exp (-r * δ)) *
          (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ + r) * Z ω)) ∂P) :=
      lintegral_const_mul _ hf
