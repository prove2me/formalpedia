-- Prove2me | solution 1 for AvramDividend.Classical.avram_redux17_original_intrinsic_marked_cutoff_laplace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:15:11.142076+00:00
-- url     : https://prove2.me/submissions/7cf1e9b9-acd8-4b44-b98a-8b35ae5d7508
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_unit_time_intrinsic_marked_laplace
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_intrinsic_integer_horizon_transform_power

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original marked Laplace identity follows from the unit-time law and the original integer-horizon semigroup. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
          p.2 < -(1 / ((k : ℝ) + 1)) then
          ENNReal.ofReal (-p.2) else 0
        ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) =
      Real.exp (-((n : ℝ) *
        (∫ y in Iio (-(1 / ((k : ℝ) + 1))), (1 - Real.exp y) ∂X.ν))) := by
  intro n k
  rw [avram_bv_jump8_intrinsic_integer_horizon_transform_power X hX hBV n k]
  rw [avram_bv_jump8_unit_time_intrinsic_marked_laplace X hX hBV k]
  rw [← Real.exp_nat_mul]
  congr 1
  ring
