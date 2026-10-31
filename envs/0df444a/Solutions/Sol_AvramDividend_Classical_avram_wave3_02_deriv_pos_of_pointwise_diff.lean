-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_deriv_pos_of_pointwise_diff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:47:24.660601+00:00
-- url     : https://prove2.me/submissions/e2d89a44-7294-4e32-b156-9fe81b1fc71a

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At each positive point where the original q-scale is differentiable,
the Esscher renewal monotonicity makes its derivative strictly positive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hdiff : DifferentiableAt ℝ W a) :
    0 < deriv W a := by
  obtain ⟨hposW, φ, hφ, hmono⟩ :=
    scaleFunction_tilted_positive_monotone X hX q hq W hW
  have hbound : φ * W a ≤ deriv W a :=
    normalized_derivative_lower_bound φ a hmono ha hdiff
  exact lt_of_lt_of_le
    (mul_pos hφ (hposW a (Set.mem_Ioi.mpr ha))) hbound
