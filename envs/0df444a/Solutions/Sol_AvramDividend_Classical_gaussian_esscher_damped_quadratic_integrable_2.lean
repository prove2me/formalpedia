-- Prove2me | solution 2 for AvramDividend.Classical.gaussian_esscher_damped_quadratic_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T11:46:42.190678+00:00
-- url     : https://prove2.me/submissions/c46115d9-1346-4f4c-9673-e6aac610831e

import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_tail_area_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_damped_square_pointwise

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- The Esscher-tilted Levy measure has finite quadratic jump mass. -/
theorem solution
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ∂μ) < ⊤ := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  let C : ℝ := 1 + 2 / φ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hmeas : Measurable
      (fun z : ℝ =>
        ENNReal.ofReal
          (Real.exp (-((φ / 2) * z)) * min (z ^ 2) z)) := by
    fun_prop
  have hmem : ∀ᵐ z : ℝ ∂ν, z ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem (μ := μ) measurableSet_Ioi
  have hpoint : ∀ᵐ z : ℝ ∂ν,
      ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal
            (Real.exp (-((φ / 2) * z)) * min (z ^ 2) z) := by
    filter_upwards [hmem] with z hz
    change 0 < z at hz
    have hb :=
      gaussian_esscher_damped_square_pointwise φ z hφ hz.le
    have hrew : -(φ * z / 2) = -((φ / 2) * z) := by ring
    rw [hrew] at hb
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hb
  have hbound :
      (∫⁻ z : ℝ,
        ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ∂ν) ≤
      ENNReal.ofReal C *
        (∫⁻ z : ℝ,
          ENNReal.ofReal
            (Real.exp (-((φ / 2) * z)) * min (z ^ 2) z) ∂ν) := by
    calc
      _ ≤ (∫⁻ z : ℝ,
            ENNReal.ofReal C *
              ENNReal.ofReal
                (Real.exp (-((φ / 2) * z)) * min (z ^ 2) z) ∂ν) :=
        lintegral_mono_ae hpoint
      _ = _ := lintegral_const_mul (ENNReal.ofReal C) hmeas
  have hφ2 : 0 < φ / 2 := by positivity
  have hbase := esscher_tilted_tail_area_integrable
    μ (φ / 2) hφ2 hlevy
  have hprod :
      ENNReal.ofReal C *
        (∫⁻ z : ℝ,
          ENNReal.ofReal
            (Real.exp (-((φ / 2) * z)) * min (z ^ 2) z) ∂ν) < ⊤ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · simpa only [ν] using hbase
  change (∫⁻ z : ℝ,
    ENNReal.ofReal (Real.exp (-(φ * z)) * z ^ 2) ∂ν) < ⊤
  exact lt_of_le_of_lt hbound hprod
