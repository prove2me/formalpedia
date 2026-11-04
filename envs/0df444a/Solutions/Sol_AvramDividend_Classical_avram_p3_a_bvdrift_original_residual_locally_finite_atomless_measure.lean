-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:40:33.392185+00:00
-- url     : https://prove2.me/submissions/3684f3e3-9d59-4fa8-8d58-7401e6b91e04

import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_residual_atomless_stieltjes_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original BV continuous drift remainder has finite mass locally. -/
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
      (∀ a b : ℝ≥0, a ≤ b → μ (Ioc a b) < ∞) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_raw_residual_atomless_stieltjes_measure X hBV]
    with ω hμ
  obtain ⟨μ, hinterval, hatom⟩ := hμ
  refine ⟨μ, hinterval, hatom, ?_⟩
  intro a b hab
  rw [hinterval a b hab]
  exact ENNReal.ofReal_lt_top
