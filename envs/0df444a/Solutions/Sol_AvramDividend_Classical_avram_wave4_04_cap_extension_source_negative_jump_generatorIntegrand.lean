-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_cap_extension_source_negative_jump_generatorIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:15:05.441056+00:00
-- url     : https://prove2.me/submissions/50dabc6a-fa51-49e3-963d-f43eae3eec30

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

/-- Capping above c leaves the compensated negative-jump integrand unchanged below c. -/
theorem solution
    (w : ℝ → ℝ) (c x z : ℝ) (hx : x < c) (hz : z ≤ 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun y => if y ≤ c then w y else w c + (y - c)) x z =
        SpectrallyNegativeLevy.generatorIntegrand w x z := by
  let v : ℝ → ℝ := fun y => if y ≤ c then w y else w c + (y - c)
  have hxv : v x = w x := by
    simp [v, le_of_lt hx]
  have hxz : v (x + z) = w (x + z) := by
    have hxc : x + z ≤ c := by linarith
    simp [v, hxc]
  have hlocal : v =ᶠ[𝓝 x] w := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    have hylt : y < c := hy
    simp [v, le_of_lt hylt]
  have hderiv : deriv v x = deriv w x := hlocal.deriv_eq
  unfold SpectrallyNegativeLevy.generatorIntegrand
  change v (x + z) - v x -
      deriv v x * z * (Ioo (-1 : ℝ) 1).indicator 1 z =
    w (x + z) - w x -
      deriv w x * z * (Ioo (-1 : ℝ) 1).indicator 1 z
  rw [hxz, hxv, hderiv]