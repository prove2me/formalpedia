-- Prove2me | solution 1 for AvramDividend.Classical.ae_rogozin_negative_slopes_of_unbounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T07:25:21.178309+00:00
-- url     : https://prove2.me/submissions/1fe03f97-836b-4563-83e0-970aa8224e97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_gaussian_component
import Theorems.Thm_AvramDividend_Classical_ae_rogozin_slopes_of_infinite_small_jumps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ C : ℝ,
      ∃ᶠ t in nhdsWithin (0 : ℝ≥0) (Ioi 0),
        X.X t ω < C * (t : ℝ) := by
  have hDisj :=
    AvramDividend.Classical.unbounded_variation_gaussian_or_infinite_small_jump_moment X hnbv
  rcases hDisj with hσ | hjump
  · exact AvramDividend.Classical.ae_rogozin_slopes_of_gaussian_component X hσ
  · exact AvramDividend.Classical.ae_rogozin_slopes_of_infinite_small_jumps X hjump
