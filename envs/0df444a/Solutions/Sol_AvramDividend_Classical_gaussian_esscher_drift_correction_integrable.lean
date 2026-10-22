-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_drift_correction_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:38:39.920303+00:00
-- url     : https://prove2.me/submissions/278ea7e2-c3c4-4d12-a4d2-61afc1120542

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_drift_truncation_envelope
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Absolute integrability of the Lévy Esscher drift correction
under the truncated-square condition. -/
theorem solution
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal
        |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ∂μ) < ⊤ := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  let C : ℝ := φ + 1 / φ
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg hφ.le (div_nonneg zero_le_one hφ.le)
  have hmeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min 1 (z ^ 2))) := by
    fun_prop
  have hmem : ∀ᵐ z : ℝ ∂ν, z ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem (μ := μ) measurableSet_Ioi
  have hpoint : ∀ᵐ z : ℝ ∂ν,
      ENNReal.ofReal
        |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ≤
        ENNReal.ofReal C * ENNReal.ofReal (min 1 (z ^ 2)) := by
    filter_upwards [hmem] with z hz
    change 0 < z at hz
    have hreal :=
      gaussian_esscher_drift_truncation_envelope φ z hφ hz.le
    change |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ≤
      C * min (z ^ 2) 1 at hreal
    rw [min_comm (z ^ 2) 1] at hreal
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hreal
  have hbound :
      (∫⁻ z : ℝ,
        ENNReal.ofReal
          |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ∂ν) ≤
        ENNReal.ofReal C *
          (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) := by
    calc
      (∫⁻ z : ℝ,
        ENNReal.ofReal
          |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ∂ν) ≤
        (∫⁻ z : ℝ, ENNReal.ofReal C *
          ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) :=
        lintegral_mono_ae hpoint
      _ = _ := lintegral_const_mul (ENNReal.ofReal C) hmeas
  have hprod :
      ENNReal.ofReal C *
        (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) < ⊤ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · simpa only [ν] using hlevy
  change (∫⁻ z : ℝ,
    ENNReal.ofReal
      |(if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)| ∂ν) < ⊤
  exact lt_of_le_of_lt hbound hprod
