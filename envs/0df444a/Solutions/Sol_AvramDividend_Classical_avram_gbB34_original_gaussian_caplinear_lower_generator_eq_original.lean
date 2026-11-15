-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB34_original_gaussian_caplinear_lower_generator_eq_original
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:43:41.492759+00:00
-- url     : https://prove2.me/submissions/329fce1a-6aef-42d2-9b9c-f48325f080a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB33_zerojump_generator_of_germs_equal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (w : ℝ → ℝ) (b y : ℝ) (hy : y < b) :
    let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
    X.generator V y = X.generator w y := by
  let V : ℝ → ℝ := fun z => if z ≤ b then w z else w b + (z - b)
  have hEv : V =ᶠ[𝓝 y] w := by
    filter_upwards [eventually_lt_nhds hy] with z hz
    simp [V, le_of_lt hz]
  exact avram_gbB33_zerojump_generator_of_germs_equal X hν V w y hEv
