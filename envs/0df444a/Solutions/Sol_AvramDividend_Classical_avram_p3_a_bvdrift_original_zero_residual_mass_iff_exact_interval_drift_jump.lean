-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_zero_residual_mass_iff_exact_interval_drift_jump
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:21:41.768943+00:00
-- url     : https://prove2.me/submissions/4f97b7ea-58eb-4d3d-b72c-532d2f249799

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Vanishing genuine residual Stieltjes mass is exactly the original BV
drift-minus-actual-jumps representation over that interval. -/
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
      (∀ a b : ℝ≥0, a ≤ b →
        (μ (Ioc a b) = 0 ↔
          (((b : ℝ) * X.drift - X.X b ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ b then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) =
          (((a : ℝ) * X.drift - X.X a ω) -
            (∑' u : ℝ≥0, if 0 < u ∧ u ≤ a then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)))) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure X hBV,
      avram_p3_a_bvdrift_original_raw_removed_residual_monotone X hBV]
    with ω hμ hmono
  obtain ⟨μ, hinterval, _hatom, _hfinite⟩ := hμ
  refine ⟨μ, hinterval, ?_⟩
  intro a b hab
  let R : ℝ≥0 → ℝ := fun t =>
    (((t : ℝ) * X.drift - X.X t ω) -
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))
  have hle : R a ≤ R b := hmono hab
  change μ (Ioc a b) = 0 ↔ R b = R a
  rw [hinterval a b hab]
  change ENNReal.ofReal (R b - R a) = 0 ↔ R b = R a
  rw [ENNReal.ofReal_eq_zero]
  constructor
  · intro hb
    exact le_antisymm (sub_nonpos.mp hb) hle
  · intro heq
    exact sub_nonpos.mpr (le_of_eq heq)
