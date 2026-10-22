-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_shifted_compensator_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:41:35.410756+00:00
-- url     : https://prove2.me/submissions/54fa287a-6b24-4ce2-8b88-51b503483279

import Mathlib.Data.Real.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_compensator_envelope
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_tail_area_integrable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- The Esscher-shifted Gaussian jump-compensator integral is finite under the Lévy condition. -/
theorem solution
    (μ : Measure ℝ) (φ θ : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal
        (Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z)) ∂μ) < ⊤ := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  let C : ℝ := θ + θ ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (Real.exp (-φ * z) * min (z ^ 2) z)) := by
    fun_prop
  have hmem : ∀ᵐ z : ℝ ∂ν, z ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem (μ := μ) measurableSet_Ioi
  have hpoint : ∀ᵐ z : ℝ ∂ν,
      ENNReal.ofReal
        (Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z)) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal (Real.exp (-φ * z) * min (z ^ 2) z) := by
    filter_upwards [hmem] with z hz
    change 0 < z at hz
    have hreal :=
      gaussian_esscher_compensator_envelope φ θ z hφ hθ hz.le
    change Real.exp (-φ * z) *
      (Real.exp (-θ * z) - 1 + θ * z) ≤
      C * (Real.exp (-φ * z) * min (z ^ 2) z) at hreal
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hreal
  have hbound :
      (∫⁻ z : ℝ, ENNReal.ofReal
        (Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z)) ∂ν) ≤
      ENNReal.ofReal C *
        (∫⁻ z : ℝ, ENNReal.ofReal
          (Real.exp (-φ * z) * min (z ^ 2) z) ∂ν) := by
    calc
      (∫⁻ z : ℝ, ENNReal.ofReal
        (Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z)) ∂ν) ≤
        (∫⁻ z : ℝ, ENNReal.ofReal C *
          ENNReal.ofReal
            (Real.exp (-φ * z) * min (z ^ 2) z) ∂ν) :=
        lintegral_mono_ae hpoint
      _ = _ := lintegral_const_mul (ENNReal.ofReal C) hmeas
  have hprod :
      ENNReal.ofReal C *
        (∫⁻ z : ℝ, ENNReal.ofReal
          (Real.exp (-φ * z) * min (z ^ 2) z) ∂ν) < ⊤ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · simpa only [ν, neg_mul] using
        esscher_tilted_tail_area_integrable μ φ hφ hlevy
  change (∫⁻ z : ℝ, ENNReal.ofReal
    (Real.exp (-φ * z) *
      (Real.exp (-θ * z) - 1 + θ * z)) ∂ν) < ⊤
  exact lt_of_le_of_lt hbound hprod
