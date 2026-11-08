-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen14_affine_small_negative_band_piecewise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:39:12.418198+00:00
-- url     : https://prove2.me/submissions/f79e32d5-69d0-4221-a582-148c14562077

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen11_piecewise_affine_positive_deriv_one
import Theorems.Thm_AvramDividend_Classical_avram_gen11_affine_interior_jump_integrand_zero
import Theorems.Thm_AvramDividend_Classical_avram_gen11_affine_crossing_jump_integrand
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
noncomputable section

/-- On the negative small-jump band, an affine payoff contributes only at ruin crossings. -/
theorem solution
    (x z : ℝ) (hx : 0 < x) (hcap : x < 1)
    (hz : z ∈ Ioo (-1 : ℝ) 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z =
        if z < -x then -1 - x - z else 0 := by
  rcases lt_trichotomy z (-x) with hcross | heq | hinter
  · rw [if_pos hcross]
    exact avram_gen11_affine_crossing_jump_integrand x z hx hz.1 hcross
  · rw [heq]
    have hsmall : -x ∈ Ioo (-1 : ℝ) 1 := ⟨by simpa [heq] using hz.1, by linarith⟩
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [avram_gen11_piecewise_affine_positive_deriv_one x hx]
    rw [Set.indicator_of_mem hsmall]
    simp [not_lt.mpr (le_of_lt hx)]
  · rw [if_neg (not_lt.mpr (le_of_lt hinter))]
    exact avram_gen11_affine_interior_jump_integrand_zero x z hx hcap hinter hz.2
