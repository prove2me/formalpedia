-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_unit_time_intrinsic_marked_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:21:49.209943+00:00
-- url     : https://prove2.me/submissions/121d8e61-7c2d-4c14-8227-3aee15937e3e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_cutoff_laplace_finite_product
import Theorems.Thm_AvramDividend_Classical_avram_redux20_original_unit_strict_product_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-! The unit-time intrinsic transform follows from the pathwise finite-product
identity and the exact joint-mark Poisson-product expectation. -/
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
        (avram_redux19_original_strict_negative_marked_times_finite X ω (1 : ℝ≥0) k).toFinset,
        Real.exp (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ∂P) := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact avram_redux20_original_strict_marked_cutoff_laplace_finite_product
          X ω (1 : ℝ≥0) k
    _ = _ := avram_redux20_original_unit_strict_product_laplace X hX hBV k
