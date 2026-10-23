-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_uncompensated_jump_large_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:20:10.93901+00:00
-- url     : https://prove2.me/submissions/561addfc-6a53-4a14-b979-88e7f01e3ead

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat07_scale_shift_weighted_abs_integral_le_min

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

-- A non-compensated negative jump of magnitude at least one has uniform L1 mass.
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ)
    (r : ℝ) (hr : 1 ≤ r) :
    (∫ x in Ioi (0 : ℝ),
      Real.exp (-(θ*x)) * |W x - W (x-r)|) ≤
      (X.ψ θ - q)⁻¹ := by
  have hrpos : 0 < r := lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) hr
  have hden : 0 ≤ (X.ψ θ - q)⁻¹ :=
    inv_nonneg.mpr (sub_nonneg.mpr hqθ.le)
  calc
    _ ≤ min 1 (θ*r) * (X.ψ θ - q)⁻¹ :=
      chat07_scale_shift_weighted_abs_integral_le_min
        X q W hW θ hθ hqθ r hrpos
    _ ≤ 1 * (X.ψ θ - q)⁻¹ :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) hden
    _ = (X.ψ θ - q)⁻¹ := one_mul _
