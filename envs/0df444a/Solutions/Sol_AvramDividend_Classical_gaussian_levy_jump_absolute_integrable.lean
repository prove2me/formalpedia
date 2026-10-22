-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_levy_jump_absolute_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:34:29.880987+00:00
-- url     : https://prove2.me/submissions/21e15a7d-3f0d-4d7c-aa9d-b8710cfede68

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_jump_truncation_envelope
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Absolute Lévy integrability of the original Gaussian jump-exponent term. -/
theorem solution (μ : Measure ℝ) (θ : ℝ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal
      |Real.exp (-θ * z) - 1 +
        θ * (if z ≤ 1 then z else 0)| ∂μ) < ⊤ := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  let C : ℝ := 1 + θ ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hm : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min 1 (z ^ 2))) := by
    fun_prop
  have hmem : ∀ᵐ z : ℝ ∂ν, z ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem (μ := μ) measurableSet_Ioi
  have hpoint : ∀ᵐ z : ℝ ∂ν,
      ENNReal.ofReal
        |Real.exp (-θ * z) - 1 +
          θ * (if z ≤ 1 then z else 0)| ≤
        ENNReal.ofReal C * ENNReal.ofReal (min 1 (z ^ 2)) := by
    filter_upwards [hmem] with z hz
    change 0 < z at hz
    have hreal :=
      gaussian_levy_jump_truncation_envelope θ z hθ hz.le
    change |Real.exp (-θ * z) - 1 +
      θ * (if z ≤ 1 then z else 0)| ≤
      C * min 1 (z ^ 2) at hreal
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hreal
  have hbound :
      (∫⁻ z : ℝ, ENNReal.ofReal
        |Real.exp (-θ * z) - 1 +
          θ * (if z ≤ 1 then z else 0)| ∂ν) ≤
        ENNReal.ofReal C *
          (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) := by
    calc
      _ ≤ (∫⁻ z : ℝ,
          ENNReal.ofReal C *
            ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) :=
        lintegral_mono_ae hpoint
      _ = _ := lintegral_const_mul (ENNReal.ofReal C) hm
  have hprod :
      ENNReal.ofReal C *
        (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) < ⊤ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · simpa only [ν] using hlevy
  change (∫⁻ z : ℝ, ENNReal.ofReal
    |Real.exp (-θ * z) - 1 +
      θ * (if z ≤ 1 then z else 0)| ∂ν) < ⊤
  exact lt_of_le_of_lt hbound hprod
