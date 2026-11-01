-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_cap_linear_extension_source_generatorIntegrable_iff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:22:02.929843+00:00
-- url     : https://prove2.me/submissions/40b62555-9406-479e-9397-76f2ab948ba5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

/-- Cap-linear continuation preserves genuine source generator-integrability on negative marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c x : ℝ) (hx : x < c) :
    X.GeneratorIntegrable
      (fun y => if y ≤ c then w y else w c + (y - c)) x ↔
        X.GeneratorIntegrable w x := by
  let v : ℝ → ℝ := fun y => if y ≤ c then w y else w c + (y - c)
  have hlocal : v =ᶠ[𝓝 x] w := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    have hylt : y < c := hy
    simp [v, le_of_lt hylt]
  have hval : v x = w x := hlocal.eq_of_nhds
  have hderiv : deriv v x = deriv w x := hlocal.deriv_eq
  have hkernel (z : ℝ) (hz : z < 0) :
      SpectrallyNegativeLevy.generatorIntegrand v x z =
        SpectrallyNegativeLevy.generatorIntegrand w x z := by
    have hxc : x + z ≤ c := by linarith
    have hxz : v (x + z) = w (x + z) := by
      simp [v, hxc]
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [hxz, hval, hderiv]
  change IntegrableOn
      (SpectrallyNegativeLevy.generatorIntegrand v x) (Iio 0) X.ν ↔
    IntegrableOn
      (SpectrallyNegativeLevy.generatorIntegrand w x) (Iio 0) X.ν
  apply integrableOn_congr_fun ?_ measurableSet_Iio
  intro z hz
  exact hkernel z hz