-- Prove2me | solution 1 for AvramDividend.Classical.bv_scale_deriv_ge_negative_jump_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T00:19:09.198192+00:00
-- url     : https://prove2.me/submissions/61aa2354-9ca6-4544-9ec8-089e014da2dd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_scale_renewal_derivative_lower_package
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- Positive BV scale renewal terms bound the scale derivative below by its jump tail. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 < x) :
    (X.ν (Iio (-x))).toReal / X.drift ^ 2 ≤ deriv W x := by
  obtain ⟨hW0, hrenewal⟩ :=
    bv_scale_renewal_derivative_lower_package X hX q hq W hW hBV
  obtain ⟨R, hR, hEq⟩ := hrenewal x hx
  have hd : 0 < X.drift := (bv_standing_drift_pos X hX hBV).1
  have hd2 : 0 < X.drift ^ 2 := sq_pos_of_pos hd
  have hqW : 0 ≤ q * W x :=
    mul_nonneg (le_of_lt hq) (hW.2.1 x (le_of_lt hx))
  have hmul :
      (X.ν (Iio (-x))).toReal / X.drift ≤ X.drift * deriv W x := by
    calc
      (X.ν (Iio (-x))).toReal / X.drift =
          (X.ν (Iio (-x))).toReal * (1 / X.drift) := by ring
      _ ≤ q * W x + (X.ν (Iio (-x))).toReal * W 0 + R := by
        rw [hW0]
        linarith
      _ = X.drift * deriv W x := hEq.symm
  apply (div_le_iff₀ hd2).2
  have := (div_le_iff₀ hd).1 hmul
  nlinarith
