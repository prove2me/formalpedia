-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen12_affine_small_negative_jump_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:53:11.540326+00:00
-- url     : https://prove2.me/submissions/bf188be7-0f84-4e2c-9311-64077ec2e109

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

/-- The ruin-crossing boundary term makes every small negative jump nonpositive. -/
theorem solution
    (x z : ℝ) (hx : 0 < x) (hcap : x < 1)
    (hzlow : -1 < z) (hzneg : z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z ≤ 0 := by
  rcases lt_trichotomy z (-x) with hcross | heq | hinter
  · rw [avram_gen11_affine_crossing_jump_integrand x z hx hzlow hcross]
    linarith
  · rw [heq]
    have hsmall : -x ∈ Ioo (-1 : ℝ) 1 := ⟨by simpa [heq] using hzlow, by linarith⟩
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [avram_gen11_piecewise_affine_positive_deriv_one x hx]
    rw [Set.indicator_of_mem hsmall]
    simp [not_lt.mpr (le_of_lt hx)]
  · rw [avram_gen11_affine_interior_jump_integrand_zero x z hx hcap hinter hzneg]
