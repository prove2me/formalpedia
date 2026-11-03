-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_zero_count_law
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:42:51.078498+00:00
-- url     : https://prove2.me/submissions/8182b2b8-fa17-4427-9efa-cef3d33187a4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_zero_horizon_intrinsic_poisson_base_from_levy_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_intrinsic_negative_band_positive_horizon_poisson_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact source count-law reduction: the zero case is Proved; positive time remains Open. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ) :
    P {ω : Ω |
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0} =
      ENNReal.ofReal (Real.exp
        (-((T : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) := by
  by_cases hZero : T = 0
  · subst T
    simpa using
      (avram_wave7_06_original_zero_horizon_intrinsic_poisson_base_from_levy_probability
        X n)
  · have hPos : 0 < T := by
      exact pos_iff_ne_zero.mpr hZero
    exact avram_wave7_06_original_intrinsic_negative_band_positive_horizon_poisson_law
      X T n hPos
