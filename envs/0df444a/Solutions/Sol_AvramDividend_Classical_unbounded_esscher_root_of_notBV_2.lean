-- Prove2me | solution 2 for AvramDividend.Classical.unbounded_esscher_root_of_notBV
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T02:31:38.635279+00:00
-- url     : https://prove2.me/submissions/016ef868-db73-41c8-9f88-16868451248a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q :=
  AvramDividend.Classical.positive_esscher_root_of_unbounded_variation X hnbv q hq
