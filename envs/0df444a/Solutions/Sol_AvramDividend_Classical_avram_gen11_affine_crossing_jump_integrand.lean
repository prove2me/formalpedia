-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen11_affine_crossing_jump_integrand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:46:10.403137+00:00
-- url     : https://prove2.me/submissions/268fb3fc-4112-42be-bda1-6eee22e6ce73

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen11_piecewise_affine_positive_deriv_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
noncomputable section

/-- The original small negative jump crossing ruin carries the unit boundary discontinuity. -/
theorem solution
    (x z : ℝ) (hx : 0 < x) (hzlow : -1 < z) (hzcross : z < -x) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z =
        -1 - x - z := by
  have hneg : x + z < 0 := by linarith
  have hsmall : z ∈ Ioo (-1 : ℝ) 1 := ⟨hzlow, by linarith⟩
  unfold SpectrallyNegativeLevy.generatorIntegrand
  rw [avram_gen11_piecewise_affine_positive_deriv_one x hx]
  rw [Set.indicator_of_mem hsmall]
  simp [hneg, not_lt.mpr (le_of_lt hx)]
  ring
