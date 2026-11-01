-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_source_jump_times_finite_on_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:46:05.624984+00:00
-- url     : https://prove2.me/submissions/2ff8d899-e929-4fa3-9672-6cb5d4e0f0ea

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_source_jump_times_finite_of_finite_range
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_finite_residual_range_on_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/--
For a genuine original-space BV spectrally negative Lévy source of finite
negative Lévy intensity, the set of actual nonzero source-X jump times on
any positive finite horizon is almost surely finite.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      {t : ℝ≥0 |
        t ≤ T ∧ 0 < t ∧
          X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0}.Finite := by
  exact
    avram_wave4_04a_bv_actual_source_jump_times_finite_of_finite_range
      X hBV T
      (avram_wave4_04a_bv_actual_finite_residual_range_on_horizon
        X hBV hFinite T hT)
