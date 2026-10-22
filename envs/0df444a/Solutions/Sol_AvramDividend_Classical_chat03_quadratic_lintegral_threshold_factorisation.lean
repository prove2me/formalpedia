-- Prove2me | solution 1 for AvramDividend.Classical.chat03_quadratic_lintegral_threshold_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T09:39:34.355603+00:00
-- url     : https://prove2.me/submissions/ce1e0396-f4c5-4b92-b8ec-d54249ec55d4

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.ENNReal.Inv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-!
Factor a constant positive threshold out of the nonnegative Lebesgue
integral of a squared random variable, including infinite moments.
-/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ) (R : ℝ) (hR : 0 < R) :
    (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2 / R) ∂P) =
      (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) / ENNReal.ofReal R := by
  have hR0 : ENNReal.ofReal R ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hR)
  have hInv : (ENNReal.ofReal R)⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr hR0
  have hpoint (ω : Ω) :
      ENNReal.ofReal ((Y ω) ^ 2 / R) =
        ENNReal.ofReal ((Y ω) ^ 2) * (ENNReal.ofReal R)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos hR]
    rfl
  calc
    (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2 / R) ∂P) =
        ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) * (ENNReal.ofReal R)⁻¹ ∂P :=
      lintegral_congr hpoint
    _ = (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) *
          (ENNReal.ofReal R)⁻¹ :=
      lintegral_mul_const' _ _ hInv
    _ = (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P) /
          ENNReal.ofReal R := rfl
