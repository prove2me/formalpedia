-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen15_affine_singular_generator_jump_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:58:11.211785+00:00
-- url     : https://prove2.me/submissions/e3a567db-9b1a-477b-9c95-3003cca22cd9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen14_affine_singular_density_generator_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The original affine generator jump integrand is integrable at every positive subunit reserve. -/
theorem solution (x : ℝ) (hx : 0 < x) (hcap : x < 1) :
    Integrable (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then 0 else 1 + u) x z)
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) := by
  let s : ℝ := x ^ (1 / 2 : ℝ)
  let v : ℝ := x ^ (-(1 / 2 : ℝ))
  have hs : 0 < s := Real.rpow_pos_of_pos hx _
  have hslt : s < 1 := Real.rpow_lt_one (le_of_lt hx) hcap (by norm_num)
  have hprod : s * v = 1 := by
    change x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1
    rw [← Real.rpow_add hx]
    norm_num
  have hfac : 0 < (1 - s) * (1 + x - s) :=
    mul_pos (by linarith) (by linarith)
  have hmul : s * (2 * (1 - s) - (1 + x) * (2 * (v - 1))) =
      -2 * (1 - s) * (1 + x - s) := by
    calc
      _ = 2 * s * (1 - s) - 2 * (1 + x) * (s * v - s) := by ring
      _ = 2 * s * (1 - s) - 2 * (1 + x) * (1 - s) := by rw [hprod]
      _ = -2 * (1 - s) * (1 + x - s) := by ring
  by_contra hn
  have hzero := integral_undef hn
  rw [avram_gen14_affine_singular_density_generator_integral x hx hcap] at hzero
  have hzero' : 2 * (1 - s) - (1 + x) * (2 * (v - 1)) = 0 := by
    simpa only [s, v] using hzero
  have hneg : s * (2 * (1 - s) - (1 + x) * (2 * (v - 1))) < 0 := by
    rw [hmul]
    nlinarith
  rw [hzero'] at hneg
  norm_num at hneg
