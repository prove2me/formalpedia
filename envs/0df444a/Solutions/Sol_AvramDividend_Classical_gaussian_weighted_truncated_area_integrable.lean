-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_weighted_truncated_area_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:17:08.940273+00:00
-- url     : https://prove2.me/submissions/c3e448d3-084a-401d-aa83-fbbc37dd1dbc

import Mathlib.Tactic
import Theorems.Thm_AvramDividend_Classical_gaussian_truncated_double_tail_area_bound
import Theorems.Thm_AvramDividend_Classical_esscher_tilted_tail_area_integrable
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

/-- The Esscher Gaussian Volterra kernel has finite truncated jump-area mass. -/
theorem solution
    (μ : Measure ℝ) (φ R : ℝ) (hφ : 0 < φ) (hR : 0 ≤ R)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal
        (Real.exp (-(φ * z)) *
          (z * min R z - (min R z) ^ 2 / 2)) ∂μ) < ⊤ := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  let C : ℝ := 1 + R
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith
  have hmeas : Measurable
      (fun z : ℝ =>
        ENNReal.ofReal (Real.exp (-(φ * z)) * min (z ^ 2) z)) := by
    fun_prop
  have hmem : ∀ᵐ z : ℝ ∂ν, z ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem (μ := μ) measurableSet_Ioi
  have hpoint : ∀ᵐ z : ℝ ∂ν,
      ENNReal.ofReal
        (Real.exp (-(φ * z)) *
          (z * min R z - (min R z) ^ 2 / 2)) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal
            (Real.exp (-(φ * z)) * min (z ^ 2) z) := by
    filter_upwards [hmem] with z hz
    change 0 < z at hz
    have ha := (gaussian_truncated_double_tail_area_bound R z hR hz.le).2
    have hr :
        Real.exp (-(φ * z)) *
          (z * min R z - (min R z) ^ 2 / 2) ≤
          C * (Real.exp (-(φ * z)) * min (z ^ 2) z) := by
      calc
        _ ≤ Real.exp (-(φ * z)) * ((1 + R) * min (z ^ 2) z) :=
          mul_le_mul_of_nonneg_left ha (Real.exp_nonneg _)
        _ = _ := by dsimp [C]; ring
    rw [← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal hr
  have hbound :
      (∫⁻ z : ℝ,
        ENNReal.ofReal
          (Real.exp (-(φ * z)) *
            (z * min R z - (min R z) ^ 2 / 2)) ∂ν) ≤
        ENNReal.ofReal C *
          (∫⁻ z : ℝ,
            ENNReal.ofReal
              (Real.exp (-(φ * z)) * min (z ^ 2) z) ∂ν) := by
    calc
      _ ≤
          (∫⁻ z : ℝ,
            ENNReal.ofReal C *
              ENNReal.ofReal
                (Real.exp (-(φ * z)) * min (z ^ 2) z) ∂ν) :=
        lintegral_mono_ae hpoint
      _ = _ := lintegral_const_mul (ENNReal.ofReal C) hmeas
  have hbase := esscher_tilted_tail_area_integrable μ φ hφ hlevy
  have hprod :
      ENNReal.ofReal C *
        (∫⁻ z : ℝ,
          ENNReal.ofReal
            (Real.exp (-(φ * z)) * min (z ^ 2) z) ∂ν) < ⊤ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.ofReal_lt_top
    · simpa only [ν] using hbase
  change (∫⁻ z : ℝ,
    ENNReal.ofReal
      (Real.exp (-(φ * z)) *
        (z * min R z - (min R z) ^ 2 / 2)) ∂ν) < ⊤
  exact lt_of_le_of_lt hbound hprod
