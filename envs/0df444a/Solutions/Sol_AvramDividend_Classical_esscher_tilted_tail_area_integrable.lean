-- Prove2me | solution 1 for AvramDividend.Classical.esscher_tilted_tail_area_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:48:58.177375+00:00
-- url     : https://prove2.me/submissions/aeaf7d82-65f6-4b7d-84a8-879e6ee8211d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_tail_scalar_integrability_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Truncated-square jump integrability controls the Esscher-damped tail area. -/
theorem solution
    (μ : Measure ℝ) (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ), ENNReal.ofReal
      (Real.exp (-(φ * z)) * min (z ^ 2) z) ∂μ) < ⊤ := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  let C : ℝ := 1 + φ⁻¹
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hmeas : Measurable
      (fun z : ℝ => ENNReal.ofReal (min 1 (z ^ 2))) := by
    fun_prop
  have hmem : ∀ᵐ z : ℝ ∂ν, z ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem (μ := μ) measurableSet_Ioi
  have hpoint : ∀ᵐ z : ℝ ∂ν,
      ENNReal.ofReal (Real.exp (-(φ * z)) * min (z ^ 2) z) ≤
        ENNReal.ofReal C * ENNReal.ofReal (min 1 (z ^ 2)) := by
    filter_upwards [hmem] with z hz
    change 0 < z at hz
    have hreal := esscher_tilted_tail_scalar_integrability_bound φ z hφ hz.le
    change Real.exp (-(φ * z)) * min (z ^ 2) z ≤ C * min 1 (z ^ 2) at hreal
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hreal
  have hbound :
      (∫⁻ z : ℝ, ENNReal.ofReal
          (Real.exp (-(φ * z)) * min (z ^ 2) z) ∂ν) ≤
        ENNReal.ofReal C *
          (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) := by
    calc
      (∫⁻ z : ℝ, ENNReal.ofReal
          (Real.exp (-(φ * z)) * min (z ^ 2) z) ∂ν) ≤
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
  change (∫⁻ z : ℝ, ENNReal.ofReal
      (Real.exp (-(φ * z)) * min (z ^ 2) z) ∂ν) < ⊤
  exact lt_of_le_of_lt hbound hprod
