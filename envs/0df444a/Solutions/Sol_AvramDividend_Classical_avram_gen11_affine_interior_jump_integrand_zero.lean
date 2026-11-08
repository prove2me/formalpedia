-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen11_affine_interior_jump_integrand_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T12:47:32.92826+00:00
-- url     : https://prove2.me/submissions/f36df86f-21f3-43c5-b063-f33271bedd89

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gen11_piecewise_affine_positive_deriv_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set
noncomputable section

/-- Small negative jumps that remain strictly solvent have zero affine generator remainder. -/
theorem solution
    (x z : ℝ) (hx : 0 < x) (hcap : x < 1)
    (hzin : -x < z) (hzneg : z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u) x z = 0 := by
  have hpositive : 0 < x + z := by linarith
  have hsmall : z ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  unfold SpectrallyNegativeLevy.generatorIntegrand
  rw [avram_gen11_piecewise_affine_positive_deriv_one x hx]
  rw [Set.indicator_of_mem hsmall]
  simp [not_lt.mpr (le_of_lt hpositive), not_lt.mpr (le_of_lt hx)]
