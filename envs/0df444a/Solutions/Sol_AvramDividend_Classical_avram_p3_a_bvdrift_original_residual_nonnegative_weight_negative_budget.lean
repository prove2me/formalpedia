-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_residual_nonnegative_weight_negative_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:09:23.550244+00:00
-- url     : https://prove2.me/submissions/ff06c959-6b6d-4d6a-a011-902b4b7f84d8

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Positive derivative weights make residual drift removal a negative budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∃ μ : Measure ℝ≥0,
      (∀ a b : ℝ≥0, a ≤ b →
        μ (Ioc a b) = ENNReal.ofReal (
          ((((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) -
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))))) ∧
      (∀ a : ℝ≥0, μ {a} = 0) ∧
      (∀ a b : ℝ≥0, a ≤ b → μ (Ioc a b) < ∞) ∧
      (∀ g : ℝ≥0 → ℝ, (∀ t, 0 ≤ g t) →
        -(∫ t, g t ∂μ) ≤ 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure X hBV]
    with ω hμ
  obtain ⟨μ, hinterval, hatom, hlocal⟩ := hμ
  refine ⟨μ, hinterval, hatom, hlocal, ?_⟩
  intro g hg
  exact neg_nonpos.mpr (integral_nonneg hg)
