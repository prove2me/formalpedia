-- Prove2me | solution 2 for AvramDividend.Classical.avram_redux17_original_intrinsic_marked_cutoff_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:10:09.718222+00:00
-- url     : https://prove2.me/submissions/76cc52e7-0779-40e3-a472-4ca15b5bb51b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_intrinsic_integer_horizon_transform_power
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_unit_time_intrinsic_marked_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Canonical original marked Laplace law reduces to its unit-time child. -/
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
  have hpow := avram_bv_jump8_intrinsic_integer_horizon_transform_power
    X hX hBV n k
  have hunit := avram_bv_jump8_unit_time_intrinsic_marked_laplace X hX hBV k
  rw [hpow, hunit]
  rw [← Real.exp_nat_mul]
  congr 1
  ring
