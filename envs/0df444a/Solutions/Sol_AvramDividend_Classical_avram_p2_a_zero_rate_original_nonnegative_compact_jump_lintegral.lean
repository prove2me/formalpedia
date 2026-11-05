-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_original_nonnegative_compact_jump_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:31:33.342209+00:00
-- url     : https://prove2.me/submissions/90e3a000-ec88-48a6-a4a7-cffd6292bbbc

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_original_uncentered_compact_negative_jump_mean
import Mathlib.Topology.Order.LeftRightLim

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Genuine nonnegative compact-mark jump expectation in ENNReal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T)
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Set.Iio (0 : ℝ))
    (hgnonneg : ∀ y : ℝ, 0 ≤ g y) :
    ∃ J : Ω → ℝ, Integrable J P ∧
      (∀ ω, ∃ F : Finset ℝ≥0,
        (∀ u : ℝ≥0, u ∈ F ↔ 0 < u ∧ u ≤ T ∧
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u) ≠ 0) ∧
        J ω = ∑ u ∈ F,
          g (X.X u ω - Function.leftLim (fun t : ℝ≥0 => X.X t ω) u)) ∧
      (∀ ω, 0 ≤ J ω) ∧
      (∫⁻ ω, ENNReal.ofReal (J ω) ∂P) =
        ENNReal.ofReal ((T : ℝ) *
          (∫ y : ℝ, g y ∂(X.ν.restrict (Set.Iio (0 : ℝ))))) := by
  classical
  obtain ⟨J, hJ, hsum, hmean⟩ :=
    avram_p2_j_ui_original_uncentered_compact_negative_jump_mean
      P X T hT g hg hc hneg
  have hnonneg : ∀ ω : Ω, 0 ≤ J ω := by
    intro ω
    obtain ⟨F, _, hJF⟩ := hsum ω
    rw [hJF]
    exact Finset.sum_nonneg (by
      intro u hu
      exact hgnonneg _)
  have hAE : ∀ᵐ ω ∂P, (0 : ℝ) ≤ J ω :=
    Filter.Eventually.of_forall hnonneg
  have hconvert :
      ENNReal.ofReal (∫ ω, J ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal (J ω) ∂P :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hJ hAE
  refine ⟨J, hJ, hsum, hnonneg, ?_⟩
  rw [← hconvert, hmean]
