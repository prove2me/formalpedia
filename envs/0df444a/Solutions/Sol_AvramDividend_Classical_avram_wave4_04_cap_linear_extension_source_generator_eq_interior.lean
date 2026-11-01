-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04_cap_linear_extension_source_generator_eq_interior
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:19:33.896266+00:00
-- url     : https://prove2.me/submissions/a9cedb92-f7ba-4b53-b11a-0b696479f775

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

/-- The source generator at a strict interior reserve ignores slope-one continuation above the cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (c x : ℝ) (hx : x < c) :
    X.generator
      (fun y => if y ≤ c then w y else w c + (y - c)) x =
        X.generator w x := by
  let v : ℝ → ℝ := fun y => if y ≤ c then w y else w c + (y - c)
  have hlocal : v =ᶠ[𝓝 x] w := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
    have hylt : y < c := hy
    simp [v, le_of_lt hylt]
  have hval : v x = w x := hlocal.eq_of_nhds
  have hderiv : deriv v x = deriv w x := hlocal.deriv_eq
  have hsecond : iteratedDeriv 2 v x = iteratedDeriv 2 w x :=
    hlocal.iteratedDeriv_eq 2
  have hkernel (z : ℝ) (hz : z < 0) :
      SpectrallyNegativeLevy.generatorIntegrand v x z =
        SpectrallyNegativeLevy.generatorIntegrand w x z := by
    have hxc : x + z ≤ c := by linarith
    have hxz : v (x + z) = w (x + z) := by
      simp [v, hxc]
    unfold SpectrallyNegativeLevy.generatorIntegrand
    rw [hxz, hval, hderiv]
  have hInt :
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand v x z ∂X.ν) =
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w x z ∂X.ν) := by
    apply setIntegral_congr_fun measurableSet_Iio
    intro z hz
    exact hkernel z hz
  change X.σ ^ 2 / 2 * iteratedDeriv 2 v x +
        X.c * deriv v x +
          (∫ z in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand v x z ∂X.ν) =
      X.σ ^ 2 / 2 * iteratedDeriv 2 w x +
        X.c * deriv w x +
          (∫ z in Iio (0 : ℝ),
            SpectrallyNegativeLevy.generatorIntegrand w x z ∂X.ν)
  rw [hsecond, hderiv, hInt]