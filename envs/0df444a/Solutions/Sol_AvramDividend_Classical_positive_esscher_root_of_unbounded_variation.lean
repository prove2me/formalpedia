-- Prove2me | solution 1 for AvramDividend.Classical.positive_esscher_root_of_unbounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:31:10.891458+00:00
-- url     : https://prove2.me/submissions/da83c2b3-0b52-4f0f-9ac8-80769e74e871

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q :=
  esscher_positive_root_of_unbounded_variation X hnbv q hq
    (levy_laplace_exponent_continuousOn_nonnegative X)
