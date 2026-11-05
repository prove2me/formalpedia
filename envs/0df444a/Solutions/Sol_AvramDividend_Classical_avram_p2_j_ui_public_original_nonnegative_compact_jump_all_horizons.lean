-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_public_original_nonnegative_compact_jump_all_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:21:23.872253+00:00
-- url     : https://prove2.me/submissions/7122d5c7-2966-4522-a4b4-d9cf2b129d6b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_nonnegative_compact_jump_lintegral
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The original nonnegative compact jump-test expectation also holds at horizon zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ → ℝ) (hf : Continuous f)
    (hc : IsCompact (tsupport f)) (hneg : tsupport f ⊆ Iio (0 : ℝ))
    (a ε : ℝ) (hε : 0 < ε)
    (hflower : ∀ y : ℝ, y < a → f y = 0)
    (hfupper : ∀ y : ℝ, -ε < y → f y = 0)
    (hXm : ∀ t : ℝ≥0, Measurable (X.X t))
    (T : ℝ≥0) (hfnonneg : ∀ y : ℝ, 0 ≤ f y) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          f (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) ∧
      (∀ ω, 0 ≤ J ω) ∧
      (∫⁻ ω, ENNReal.ofReal (J ω) ∂P) =
        ENNReal.ofReal ((T : ℝ) *
          (∫ y : ℝ, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) := by
  by_cases hT : T = 0
  · subst T
    refine ⟨fun _ => 0, integrable_zero Ω ℝ P, ?_, ?_, ?_⟩
    · intro ω
      refine ⟨∅, ?_, by simp⟩
      intro u
      constructor
      · intro huF
        simp at huF
      · intro hu
        exact False.elim ((not_lt_of_ge hu.2.1) hu.1)
    · intro ω
      exact le_refl _
    · simp
  · have hTpos : 0 < T := pos_iff_ne_zero.mpr hT
    exact avram_p2_j_ui_public_original_nonnegative_compact_jump_lintegral
      P X f hf hc hneg a ε hε hflower hfupper hXm T hTpos hfnonneg
