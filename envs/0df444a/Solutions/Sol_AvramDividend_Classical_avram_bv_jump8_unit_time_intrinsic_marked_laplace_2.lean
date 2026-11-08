-- Prove2me | solution 2 for AvramDividend.Classical.avram_bv_jump8_unit_time_intrinsic_marked_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:22:25.812831+00:00
-- url     : https://prove2.me/submissions/15e3f5c2-ee49-4d19-a61c-7bdf525c5279

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_cutoff_laplace_finite_product
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_unit_strict_product_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Reduce the actual intrinsic marked Laplace identity to the finite physical
jump-product law, using the already-proved exact pathwise marked identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
          p.2 < -(1 / ((k : ℝ) + 1)) then
          ENNReal.ofReal (-p.2) else 0
        ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) =
        Real.exp (-(∫ y in Iio (-(1 / ((k : ℝ) + 1))),
          (1 - Real.exp y) ∂X.ν)) := by
  intro k
  calc
    (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
        p.2 < -(1 / ((k : ℝ) + 1)) then
        ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) =
        (∫ ω : Ω, ∏ u ∈
          (avram_redux19_original_strict_negative_marked_times_finite
            X ω (1 : ℝ≥0) k).toFinset,
          Real.exp (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      exact avram_redux20_original_strict_marked_cutoff_laplace_finite_product
        X ω (1 : ℝ≥0) k
    _ = Real.exp (-(∫ y in Iio (-(1 / ((k : ℝ) + 1))),
        (1 - Real.exp y) ∂X.ν)) :=
      avram_redux20_original_unit_strict_product_laplace X hX hBV k
