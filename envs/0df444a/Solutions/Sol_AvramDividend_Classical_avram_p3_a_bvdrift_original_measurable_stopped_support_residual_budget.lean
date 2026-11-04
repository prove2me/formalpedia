-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_a_bvdrift_original_measurable_stopped_support_residual_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:19:06.446299+00:00
-- url     : https://prove2.me/submissions/2294c761-e2c4-4572-ab55-172b2ea4eada

import Mathlib
import Mathlib.MeasureTheory.Measure.Stieltjes
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Any measurable stopped support with a nonnegative derivative weight has
a nonpositive signed contribution from the genuine continuous BV remainder. -/
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
      (∀ S : Set ℝ≥0, MeasurableSet S →
        ∀ g : ℝ≥0 → ℝ, (∀ t ∈ S, 0 ≤ g t) →
          -(∫ t in S, g t ∂μ) ≤ 0) := by
  filter_upwards
    [avram_p3_a_bvdrift_original_residual_locally_finite_atomless_measure X hBV]
    with ω hμ
  obtain ⟨μ, hinterval, hatom, hlocal⟩ := hμ
  refine ⟨μ, hinterval, hatom, hlocal, ?_⟩
  intro S hS g hg
  have hnonneg : ∀ t : ℝ≥0, 0 ≤ S.indicator g t := by
    intro t
    by_cases ht : t ∈ S
    · simpa only [Set.indicator_of_mem ht] using hg t ht
    · simp only [Set.indicator_of_notMem ht, le_refl]
  have hI : 0 ≤ ∫ t, S.indicator g t ∂μ := integral_nonneg hnonneg
  rw [integral_indicator hS] at hI
  exact neg_nonpos.mpr hI
