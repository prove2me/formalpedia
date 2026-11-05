-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_finite_band_rate_square_ennreal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:25:25.761415+00:00
-- url     : https://prove2.me/submissions/c686c933-3ebd-4a19-bbd7-4df963ec577c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (hν : X.ν (Iic (-(1 / ((n : ℝ) + 1)))) < ⊤) :
    ENNReal.ofReal
      ((((T : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal) ^ 2) / 2) =
      (((T : ℝ≥0∞) *
        X.ν (Iic (-(1 / ((n : ℝ) + 1))))) ^ 2) / 2 := by
  have hnonneg : 0 ≤ (T : ℝ) *
      (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal :=
    mul_nonneg (by positivity) ENNReal.toReal_nonneg
  have hprod :
      ENNReal.ofReal ((T : ℝ) *
        (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal) =
        (T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1)))) := by
    rw [ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.ofReal_toReal (ne_of_lt hν)]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  rw [ENNReal.ofReal_pow hnonneg]
  rw [hprod] <;> norm_num
