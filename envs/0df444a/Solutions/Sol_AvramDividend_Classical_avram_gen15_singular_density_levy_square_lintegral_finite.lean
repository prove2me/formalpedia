-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen15_singular_density_levy_square_lintegral_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:25:17.957665+00:00
-- url     : https://prove2.me/submissions/e46d9fc4-c401-4749-9c2b-5a519dbf2484

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gen14_singular_levy_square_jump_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The literal singular negative jump measure satisfies the original Levy moment field. -/
theorem solution :
    (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂
      (volume.withDensity (fun z : ℝ =>
        if z ∈ Ioo (-1 : ℝ) 0
        then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))) < ⊤ := by
  let ν : Measure ℝ := volume.withDensity (fun z : ℝ =>
    if z ∈ Ioo (-1 : ℝ) 0
    then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)
  change (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) < ⊤
  have hm : (∫ z : ℝ, |z| ^ (2 : ℕ) ∂ν) = 2 / 3 := by
    simpa only [ν] using avram_gen14_singular_levy_square_jump_moment
  have hfi : Integrable (fun z : ℝ => |z| ^ (2 : ℕ)) ν := by
    by_contra h
    have hz : (∫ z : ℝ, |z| ^ (2 : ℕ) ∂ν) = 0 := integral_undef h
    rw [hm] at hz
    norm_num at hz
  have hfi_sq : Integrable (fun z : ℝ => z ^ (2 : ℕ)) ν := by
    simpa only [sq_abs] using hfi
  have hm_sq : (∫ z : ℝ, z ^ (2 : ℕ) ∂ν) = 2 / 3 := by
    simpa only [sq_abs] using hm
  have htotal : (∫⁻ z : ℝ, ENNReal.ofReal (z ^ 2) ∂ν) =
      ENNReal.ofReal (2 / 3 : ℝ) := by
    calc
      _ = ENNReal.ofReal (∫ z : ℝ, z ^ 2 ∂ν) :=
        (ofReal_integral_eq_lintegral_ofReal hfi_sq
          (Filter.Eventually.of_forall (fun z => sq_nonneg z))).symm
      _ = ENNReal.ofReal (2 / 3 : ℝ) := by rw [hm_sq]
  calc
    (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂ν) ≤
        (∫⁻ z : ℝ, ENNReal.ofReal (z ^ 2) ∂ν) :=
          lintegral_mono (fun z => ENNReal.ofReal_le_ofReal (min_le_right _ _))
    _ = ENNReal.ofReal (2 / 3 : ℝ) := htotal
    _ < ⊤ := ENNReal.ofReal_lt_top
